package org.archware.sosadl.design;

import org.archware.sosadl.sosADL.ArchBehaviorDecl;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.validation.TypeInformation;
import org.eclipse.emf.common.util.BasicEList;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;

/**
 * The services class used by VSM.
 */
public class Services {
    
    /**
    * See http://help.eclipse.org/neon/index.jsp?topic=%2Forg.eclipse.sirius.doc%2Fdoc%2Findex.html&cp=24 for documentation on how to write service methods.
    */
    public SystemDecl findConstituent(EObject self, String name) {
    	SosADL model;

    	EObject current = self;
    	while (current.eClass().getName() != "SosADL") {
    		current = current.eContainer();
    	}
    	// Current poits to SosADL
    	model = (SosADL) current;

    	EntityBlock block = model.getContent().getDecls();
    	for (SystemDecl i : block.getSystems()) {
    		if (i.getName().equals(name)) return i;
    	}

    	return null;
    }
    
    public EList<SystemDecl> getConstituent(EObject self) {
    	// self is an ArchBehaviorDecl
    	ArchBehaviorDecl b = (ArchBehaviorDecl) self;
    	EList<SystemDecl> s = new BasicEList<SystemDecl>();
    	
    	for (Constituent c : b.getConstituents()) {
    		String value = ((IdentExpression) c.getValue()).getIdent();
    		SystemDecl sys = findConstituent(b, value);
    		if (sys!=null) s.add(sys); 
    	}
    	return s;
    }
    
    public EList<GateDecl> getGates(Constituent c) {
    	//Constituent c = (Constituent) obj;
    	String sysname = ((IdentExpression) c.getValue()).getIdent(); 
    	SystemDecl sys = findConstituent(c, sysname); 
    	
    	return sys.getGates();
    }

    public EList<GateDecl> allGates(Constituent c) {
    	EObject e = TypeInformation.resolve((IdentExpression) c.getValue());
    	System.out.println(e);
    	return null;
    }
    
}
