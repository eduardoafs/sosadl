package org.archware.sosadl.validation.typing.proof;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Optional;

import org.archware.sosadl.validation.typing.proof.fields.FieldDescriptor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

public class ProofTermPlaceHolder<T extends ProofTerm> implements ProofTerm {
	private final Class<T> clazz;
	private Optional<T> proxy;
	
	protected ProofTermPlaceHolder(Class<T> clazz) {
		this.clazz = clazz;
		this.proxy = Optional.empty();
	}
	
	public void fillWith(T p) {
		if(clazz.isInstance(p)) {
			this.proxy = Optional.of(p);
		} else {
			throw new IllegalArgumentException("Not an instance of " + clazz.toString());
		}
	}
	
	public T cast() {
		return clazz.cast(this);
	}

	@Override
	public String getConstructorName() {
		return this.proxy.get().getConstructorName();
	}

	@Override
	public FieldDescriptor[] getDeclaredFields() {
		return this.proxy.get().getDeclaredFields();
	}

	@Override
	public FieldDescriptor describeField(Field f) {
		return this.proxy.get().describeField(f);
	}
	
	private static HashMap<Class<? extends ProofTerm>,Constructor<ProofTermPlaceHolder<?>>> classes = new HashMap<>();
	
	public static <T extends ProofTerm> ProofTermPlaceHolder<T> create(Class<T> itf) {
		synchronized(classes) {
			while(classes.get(itf) == null) {
				try {
					classes.put(itf, generateFor(itf));
				} catch (NoSuchMethodException | SecurityException e) {
					throw new IllegalArgumentException(e);
				}
			}
			Constructor<ProofTermPlaceHolder<?>> c = (Constructor<ProofTermPlaceHolder<?>>)classes.get(itf);
			try {
				@SuppressWarnings("unchecked")
				ProofTermPlaceHolder<T> instance = (ProofTermPlaceHolder<T>) c.newInstance();
				return instance;
			} catch (InstantiationException | IllegalAccessException | IllegalArgumentException
					| InvocationTargetException e) {
				throw new IllegalArgumentException(e);
			}
		}
	}

	private static <T extends ProofTerm> Constructor<ProofTermPlaceHolder<?>> generateFor(Class<T> itf) throws NoSuchMethodException, SecurityException {
		ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS);
		String ptphName = Type.getInternalName(ProofTermPlaceHolder.class);
		String name = generateNameFor(itf);
		cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, name, null, ptphName, new String[] { Type.getInternalName(itf) });
		String ctorName = "<init>";
		String ctorDesc = Type.getConstructorDescriptor(ProofTermPlaceHolder.class.getDeclaredConstructor(Class.class));
		MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PUBLIC, ctorName, "()V", null, null);
		mv.visitParameter("c", 0);
		mv.visitCode();
		mv.visitIntInsn(Opcodes.ALOAD, 0);
		mv.visitLdcInsn(Type.getType(itf));
		mv.visitMethodInsn(Opcodes.INVOKESPECIAL, ptphName, ctorName, ctorDesc, false);
		mv.visitInsn(Opcodes.RETURN);
		mv.visitMaxs(0, 0);
		mv.visitEnd();
		cw.visitEnd();
		MyClassLoader mcl = new MyClassLoader();
		Class<?> clazz = mcl.defineClass(name, cw.toByteArray());
		assert itf.isAssignableFrom(clazz);
		@SuppressWarnings("unchecked")
		Class<ProofTermPlaceHolder<?>> cl = (Class<ProofTermPlaceHolder<?>>) clazz.asSubclass(ProofTermPlaceHolder.class); 
		return cl.getConstructor();
	}

	private static String generateNameFor(Class<?> itf) {
		StringBuilder sb = new StringBuilder("Generated_");
		for(char x: itf.getName().toCharArray()) {
			if(x >= 'A' && x <= 'Z') {
				sb.append(x);
			} else if(x >= 'a' && x <= 'z') {
				sb.append(x);
			} else if(x >= '0' && x <= '9') {
				sb.append(x);
			} else if(x == '.') {
				sb.append("__");
			} else {
				sb.append('_');
				sb.append(Integer.toHexString(x));
				sb.append('_');
			}
		}
		return sb.toString();
	}
	
	private static class MyClassLoader extends ClassLoader {
		public MyClassLoader() {
			super(MyClassLoader.class.getClassLoader());
		}
		
		public Class<?> defineClass(String name, byte[] bc) {
			return super.defineClass(name, bc, 0, bc.length);
		}
	}
}
