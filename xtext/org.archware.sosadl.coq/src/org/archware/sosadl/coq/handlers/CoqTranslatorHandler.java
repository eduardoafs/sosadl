package org.archware.sosadl.coq.handlers;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.archware.sosadl.generator.SosADL2CoqGenerator;
import org.archware.sosadl.sosADL.SosADL;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * 
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class CoqTranslatorHandler extends AbstractHandler {

	/**
	 * The constructor.
	 */
	public CoqTranslatorHandler() {
	}

	/**
	 * the command has been executed, so extract extract the needed information
	 * from the application context.
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		ISelection sel = HandlerUtil.getActiveMenuSelection(event);
		IStructuredSelection selection = (IStructuredSelection) sel;
		for (Object i : selection.toArray()) {
			try {
				translateObject(i);
			} catch (CoreException e) {
				throw new ExecutionException("", e);
			}
		}

		return null;
	}

	private void translateObject(Object i) throws CoreException {
		if (i instanceof IFile) {
			translate((IFile) i);
		} else if (i instanceof IFolder) {
			translate((IFolder) i);
		} else if (i instanceof IPackageFragmentRoot) {
			translate((IPackageFragmentRoot) i);
		} else {
			throw new ClassCastException(i.getClass().toString());
		}
	}

	private void translate(IPackageFragmentRoot i) throws JavaModelException,
			CoreException {
		translateResource(i.getCorrespondingResource());
	}

	private void translateResource(IResource i) throws CoreException {
		if (i instanceof IFile) {
			translate((IFile) i);
		} else if (i instanceof IFolder) {
			translate((IFolder) i);
		} else {
			throw new ClassCastException(i.getClass().toString());
		}
	}

	private void translate(IFolder i) throws CoreException {
		for (IResource j : i.members()) {
			translateResource(j);
		}
	}

	private void translate(IFile i) {
		ResourceSet rs = new ResourceSetImpl();
		String location = i.getLocationURI().toString();
		Resource r = rs.getResource(URI.createURI(location), true);
		SosADL2CoqGenerator gen = new SosADL2CoqGenerator();
		IPath path = new Path(i.getRawLocation().lastSegment())
				.removeFileExtension().addFileExtension("v");
		IFile j = i.getParent().getFile(path);
		SosADL sos = (SosADL) r.getContents().get(0);
		CharSequence coq = gen.compile(sos);
		try (InputStream in = new ByteArrayInputStream(coq.toString().getBytes(
				"UTF-8"))) {
			if (j.exists()) {
				// TODO
				j.setContents(in, IResource.FORCE, null);
			} else {
				j.create(in, IResource.FORCE | IResource.DERIVED, null);
			}
		} catch (IOException | CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
