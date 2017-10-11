/*
 * generated by Xtext 2.9.1
 */
package org.archware.sosadl.generator

import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.AbstractGenerator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.generator.IGeneratorContext
import com.google.inject.Inject

/**
 * Generates code from your model files on save.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#code-generation
 */
class SosADLGenerator extends AbstractGenerator {

  @Inject SosADLPrettyPrinterGenerator gen1
  @Inject SosADL2IOSTSGenerator gen2
  @Inject TypingProofGenerator gen3
  @Inject TestGenerator gen4
  
  override void doGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
    gen1.doGenerate(resource, fsa)
    gen2.doGenerate(resource, fsa)
    gen3.doGenerate(resource, fsa)
    gen4.doGenerate(resource, fsa)
  }
}
