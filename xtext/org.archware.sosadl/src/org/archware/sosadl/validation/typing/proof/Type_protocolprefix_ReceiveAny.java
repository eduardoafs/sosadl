package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.ModeType;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

import java.math.BigInteger;

public class Type_protocolprefix_ReceiveAny implements Type_protocolprefix_other {
    @Mandatory
    private final Environment gamma;

    @Mandatory
    private final String gd;

    private final EList<Connection> endpoints;

    @Mandatory
    private final boolean is_env;

    @Mandatory
    private final String conn;

    @Mandatory
    private final ModeType mode;;

    @Mandatory
    private final DataType conn__tau;

    @Mandatory
    private final Equality p1;

    @Mandatory
    private final Ex<BigInteger, Equality> p2;

    @Mandatory
    private final Mode_receive p3;

    public Type_protocolprefix_ReceiveAny(Environment gamma, String gd, EList<Connection> endpoints, boolean is_env, String conn, ModeType mode, DataType conn__tau, Equality p1, Ex<BigInteger, Equality> p2, Mode_receive p3) {
        this.gamma = gamma;
        this.gd = gd;
        this.endpoints = endpoints;
        this.is_env = is_env;
        this.conn = conn;
        this.mode = mode;
        this.conn__tau = conn__tau;
        this.p1 = p1;
        this.p2 = p2;
        this.p3 = p3;
    }

    public Environment getGamma() {
        return gamma;
    }

    public String getGd() {
        return gd;
    }

    public EList<Connection> getEndpoints() {
        return endpoints;
    }

    public boolean is_env() {
        return is_env;
    }

    public String getConn() {
        return conn;
    }

    public ModeType getMode() {
        return mode;
    }

    public DataType getConn__tau() {
        return conn__tau;
    }

    public Equality getP1() {
        return p1;
    }

    public Ex<BigInteger, Equality> getP2() {
        return p2;
    }

    public Mode_receive getP3() {
        return p3;
    }
}

