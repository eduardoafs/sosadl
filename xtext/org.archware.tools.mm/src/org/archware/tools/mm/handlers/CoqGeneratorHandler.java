package org.archware.tools.mm.handlers;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.archware.tools.mm.generators.CoqGenerator;
import org.archware.tools.mm.tools.Loader;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.EcorePackage;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * 
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class CoqGeneratorHandler extends AbstractHandler {
	/**
	 * The constructor.
	 */
	public CoqGeneratorHandler() {
	}

	/**
	 * the command has been executed, so extract extract the needed information
	 * from the application context.
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		ISelection sel = HandlerUtil.getActiveMenuSelection(event);
		IStructuredSelection selection = (IStructuredSelection) sel;
		Object firstElement = selection.getFirstElement();

		if (firstElement instanceof IFile) {
			IFile file = (IFile) firstElement;
			EPackage pkg = Loader.load(file.getLocationURI().toString());
			EList<EClassifier> classifiers = pkg.getEClassifiers();

			// Only classes and enumeration types
			if (classifiers
					.stream()
					.filter((i) -> !(i instanceof EEnum || i instanceof EClass))
					.count() == 0l) {
				// Collect enumeration types
				List<EEnum> enums = classifiers.stream()
						.filter((i) -> i instanceof EEnum)
						.map((i) -> (EEnum) i).collect(Collectors.toList());

				// Collect the classes
				Collection<EClass> classes = classifiers.stream()
						.filter((i) -> i instanceof EClass)
						.map((i) -> (EClass) i).collect(Collectors.toList());

				Map<String, EClass> namedClasses = new TreeMap<>();
				Map<String, Set<String>> subclasses = new TreeMap<>();
				Map<String, Set<String>> cases = new TreeMap<>();

				// Build a map from class name to class
				classes.forEach((i) -> {
					namedClasses.put(i.getName(), i);
					subclasses.put(i.getName(), new TreeSet<>());
					cases.put(i.getName(), new TreeSet<>());
				});
				// Collect all the subclasses of each class
				classes.forEach((i) -> i.getEAllSuperTypes().forEach(
						(j) -> subclasses.get(j.getName()).add(i.getName())));
				// Constructors are classes with no subclass
				Set<String> constructors = subclasses.entrySet().stream()
						.filter((i) -> i.getValue().isEmpty())
						.map(Map.Entry<String, Set<String>>::getKey)
						.collect(Collectors.toSet());
				// Collect case classes:
				// 1) for each class with subclasses, the case classes are
				// subclasses that are constructors
				constructors
						.stream()
						.map(namedClasses::get)
						.forEach(
								(i) -> i.getEAllSuperTypes()
										.stream()
										.forEach(
												(j) -> cases.get(j.getName())
														.add(i.getName())));
				// 2) constructors with no super class are single-case case
				// classes
				constructors.stream().map(namedClasses::get)
						.filter((i) -> i.getEAllSuperTypes().isEmpty())
						.map(EClass::getName)
						.forEach((i) -> cases.get(i).add(i));
				// 3) constructors that appear as the type of a structural
				// feature of a constructor are single-case classes
				constructors.stream().map(namedClasses::get)
						.map(EClass::getEAllStructuralFeatures)
						.flatMap(Collection<EStructuralFeature>::stream)
						.map(EStructuralFeature::getEType)
						.map(EClassifier::getName)
						.filter(constructors::contains)
						.forEach((i) -> cases.get(i).add(i));

				cases.entrySet().stream().filter((i) -> i.getValue().isEmpty())
						.map(Map.Entry<String, Set<String>>::getKey)
						.collect(Collectors.toList()).forEach(cases::remove);

				if (checkForLiteralOrClassifier(enums, namedClasses, cases,
						constructors)) {
					// Everything is OK, all the types involved in structural
					// features are either:
					// - one of enums
					// - one of case classes
					// - one literal, either EBoolean, EInt or EString
					writeCoqFile(event, file, classifiers, enums, namedClasses,
							cases);
				} else {
					IWorkbenchWindow window = HandlerUtil
							.getActiveWorkbenchWindowChecked(event);
					MessageDialog
							.openError(
									window.getShell(),
									"Mm",
									"Some structural features are neither EString, EInt, EBoolean, nor any of the meta-model classifiers");
				}
			} else {
				IWorkbenchWindow window = HandlerUtil
						.getActiveWorkbenchWindowChecked(event);
				MessageDialog
						.openError(window.getShell(), "Mm",
								"The meta-model contains some non-enum non-class classifiers");
			}
		} else {
			IWorkbenchWindow window = HandlerUtil
					.getActiveWorkbenchWindowChecked(event);
			MessageDialog.openError(window.getShell(), "Mm",
					"Select an Ecore meta-model file");
		}

		return null;
	}

	private void writeCoqFile(ExecutionEvent event, IFile file,
			EList<EClassifier> classifiers, List<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases)
			throws ExecutionException {
		IPath path = new Path(file.getRawLocation().lastSegment())
				.removeFileExtension().addFileExtension("v");
		IFile vfile = file.getParent().getFile(path);
		IWorkbenchWindow window = HandlerUtil
				.getActiveWorkbenchWindowChecked(event);
		boolean exists = vfile.exists();
		boolean doWriteCoq = !exists
				|| MessageDialog.openConfirm(window.getShell(), "Mm",
						"Do you want to overwrite "
								+ vfile.getLocationURI().toString() + "?");
		if (doWriteCoq) {
			CoqGenerator coqGenerator = new CoqGenerator(classifiers, enums,
					namedClasses, cases);
			try (InputStream in = new ByteArrayInputStream(coqGenerator
					.generate().toString().getBytes("UTF-8"))) {
				if (exists) {
					vfile.setContents(in, IResource.FORCE, null);
				} else {
					vfile.create(in, IResource.FORCE | IResource.DERIVED, null);
				}
			} catch (IOException | CoreException e) {
				throw new ExecutionException("Writing output", e);
			}
		}
	}

	private static boolean checkForLiteralOrClassifier(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			Set<String> constructors) {
		return constructors
				.stream()
				.map(namedClasses::get)
				.allMatch(
						(i) -> checkForLiteralOrClassifier(enums, namedClasses,
								cases, i));
	}

	@SuppressWarnings("unused")
	private static void dumpBad(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			Set<String> constructors) {
		constructors.stream().map(namedClasses::get).forEach((i) -> {
			if (!checkForLiteralOrClassifier(enums, namedClasses, cases, i)) {
				dumpBad(enums, namedClasses, cases, i);
			}
		});
	}

	private static boolean checkForLiteralOrClassifier(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			EClass i) {
		return i.getEAllStructuralFeatures()
				.stream()
				.map(EStructuralFeature::getEType)
				.allMatch(
						(j) -> isLiteralOrClassifier(enums, namedClasses,
								cases, j));
	}

	private static void dumpBad(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			EClass i) {
		System.out.println(i.getName()
				+ ": "
				+ i.getEAllStructuralFeatures().stream()
						.map(EStructuralFeature::getEType)
						.map((j) -> nameWithBad(enums, namedClasses, cases, j))
						.collect(Collectors.joining(" ")));
	}

	private static String nameWithBad(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			EClassifier j) {
		if (isLiteralOrClassifier(enums, namedClasses, cases, j)) {
			return j.getName();
		} else {
			return "(bad: " + j.getName() + ")";
		}
	}

	private static boolean isLiteralOrClassifier(Collection<EEnum> enums,
			Map<String, EClass> namedClasses, Map<String, Set<String>> cases,
			EClassifier j) {
		return j == EcorePackage.Literals.ESTRING
				|| j == EcorePackage.Literals.EINT
				|| j == EcorePackage.Literals.EBOOLEAN
				|| enums.contains(j)
				|| (cases.containsKey(j.getName()) && namedClasses.get(j
						.getName()) == j);
	}

	@SuppressWarnings("unused")
	private static void dumpCaseClasses(Map<String, Set<String>> cases) {
		cases.entrySet()
				.stream()
				.filter((i) -> !i.getValue().isEmpty())
				.forEach(
						(i) -> {
							System.out.println(i.getKey()
									+ ": "
									+ i.getValue().stream()
											.collect(Collectors.joining(" | ")));
						});
	}
}
