package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.ModeType;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;

import java.math.BigInteger;

public class Type_generic_Receive<Body extends EObject, Statement extends EObject, Command extends EObject, Action extends EObject, Choose extends EObject, DoExpr extends EObject, ForEach extends EObject, IfThenElse extends EObject, Valuin extends EObject, Send extends EObject, Receive extends EObject, O extends ProofTerm, E extends ProofTerm, NP extends ProofTerm>
        implements
        Type_generic_prefixstatement<Body, Statement, Command, Action, Choose, DoExpr, ForEach, IfThenElse, Valuin, Send, Receive, O, E, NP> {
    @CoqLiteral
    @Mandatory
    private final String block;

    @CoqLiteral
    @Mandatory
    private final Class<Action> action;

    @CoqLiteral
    @Mandatory
    private final Class<Choose> choose;

    @CoqLiteral
    @Mandatory
    private final Class<DoExpr> doExpr;

    @CoqLiteral
    @Mandatory
    private final Class<ForEach> forEach;

    @CoqLiteral
    @Mandatory
    private final Class<IfThenElse> ifThenElse;

    @CoqLiteral
    @Mandatory
    private final Class<Valuin> valuing;

    @CoqLiteral
    @Mandatory
    private final Class<Send> send;

    @CoqLiteral
    @Mandatory
    private final Class<Receive> receive;

    @CoqLiteral
    @Mandatory
    private final Class<O> other;

    @CoqLiteral
    @Mandatory
    private final Class<E> type_expression;

    @CoqLiteral
    @Mandatory
    private final Class<NP> type_nonfinalbody;

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
    private final ModeType mode;

    @Mandatory
    private final DataType conn__tau;

    @Mandatory
    private final String x;

    @Mandatory
    private final Environment gamma1;

    @Mandatory
    private final Equality p1;

    @Mandatory
    private final Ex<BigInteger, Equality> p2;

    @Mandatory
    private final Mode_receive p3;

    @Mandatory
    private final Equality p4;

    public Type_generic_Receive(String block, Class<Action> action, Class<Choose> choose, Class<DoExpr> doExpr, Class<ForEach> forEach, Class<IfThenElse> ifThenElse, Class<Valuin> valuing, Class<Send> send, Class<Receive> receive, Class<O> other, Class<E> type_expression, Class<NP> type_nonfinalbody, Environment gamma, String gd, EList<Connection> endpoints, boolean is_env, String conn, ModeType mode, DataType conn__tau, String x, Environment gamma1, Equality p1, Ex<BigInteger, Equality> p2, Mode_receive p3, Equality p4) {
        this.block = block;
        this.action = action;
        this.choose = choose;
        this.doExpr = doExpr;
        this.forEach = forEach;
        this.ifThenElse = ifThenElse;
        this.valuing = valuing;
        this.send = send;
        this.receive = receive;
        this.other = other;
        this.type_expression = type_expression;
        this.type_nonfinalbody = type_nonfinalbody;
        this.gamma = gamma;
        this.gd = gd;
        this.endpoints = endpoints;
        this.is_env = is_env;
        this.conn = conn;
        this.mode = mode;
        this.conn__tau = conn__tau;
        this.x = x;
        this.gamma1 = gamma1;
        this.p1 = p1;
        this.p2 = p2;
        this.p3 = p3;
        this.p4 = p4;
    }

    public String getBlock() {
        return block;
    }

    public Class<Action> getAction() {
        return action;
    }

    public Class<Choose> getChoose() {
        return choose;
    }

    public Class<DoExpr> getDoExpr() {
        return doExpr;
    }

    public Class<ForEach> getForEach() {
        return forEach;
    }

    public Class<IfThenElse> getIfThenElse() {
        return ifThenElse;
    }

    public Class<Valuin> getValuing() {
        return valuing;
    }

    public Class<Send> getSend() {
        return send;
    }

    public Class<Receive> getReceive() {
        return receive;
    }

    public Class<O> getOther() {
        return other;
    }

    public Class<E> getType_expression() {
        return type_expression;
    }

    public Class<NP> getType_nonfinalbody() {
        return type_nonfinalbody;
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

    public String getX() {
        return x;
    }

    public Environment getGamma1() {
        return gamma1;
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

    public Equality getP4() {
        return p4;
    }
}
