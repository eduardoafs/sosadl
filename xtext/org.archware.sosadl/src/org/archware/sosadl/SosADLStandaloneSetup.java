/*
* generated by Xtext
*/
package org.archware.sosadl;

/**
 * Initialization support for running Xtext languages 
 * without equinox extension registry
 */
public class SosADLStandaloneSetup extends SosADLStandaloneSetupGenerated{

	public static void doSetup() {
		new SosADLStandaloneSetup().createInjectorAndDoEMFRegistration();
	}
}
