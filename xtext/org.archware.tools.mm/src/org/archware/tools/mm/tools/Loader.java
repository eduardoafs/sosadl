package org.archware.tools.mm.tools;

import org.eclipse.emf.codegen.ecore.genmodel.GenModel;
import org.eclipse.emf.codegen.ecore.genmodel.GenPackage;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;

public class Loader {
	private static GenModel loadGenModel(ResourceSet resourceset,
			URI genModelUri) {
		Resource genModel = resourceset.getResource(genModelUri, true);
		for (EObject eo : genModel.getContents()) {
			if (eo instanceof GenModel) {
				return (GenModel) eo;
			}
		}
		return null;
	}

	public static GenPackage loadGenPackage(ResourceSet resourceset,
			URI genModelUri) {
		GenModel genModel = loadGenModel(resourceset, genModelUri);
		if (genModel != null) {
			for (GenPackage genpack : genModel
					.getAllGenPackagesWithClassifiers()) {
				return genpack;
			}
		}
		return null;
	}

	public static EPackage loadPackage(ResourceSet resourceset, URI genModelUri) {
		GenPackage genPack = loadGenPackage(resourceset, genModelUri);
		if (genPack != null) {
			return genPack.getEcorePackage();
		}
		return null;
	}
}
