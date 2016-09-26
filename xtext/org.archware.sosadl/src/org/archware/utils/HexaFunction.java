package org.archware.utils;

@FunctionalInterface
public interface HexaFunction<S1, S2, S3, S4, S5, S6, R> {
	R apply(S1 s1, S2 s2, S3 s3, S4 s4, S5 s5, S6 s6);
}
