#!/bin/bash
rem// config start
set JAVA_HOME=/home/banchuen/jdk1.8.0_65/
set SOSADLCLI_HOME=/home/banchuen/sosadlcli
set ECLIPSE_PLUGINS=%SOSADLCLI_HOME/lib/eclipse/plugins
rem// config end
rem
set CLASSPATH=%ECLIPSE_PLUGINS%/ee.minimum-1.0.0.jar:%ECLIPSE_PLUGINS%/org.eclipse.emf.common_2.11.0.v20150805-0538.jar:%ECLIPSE_PLUGINS%/org.eclipse.emf.ecore_2.11.1.v20150805-0538.jar:%ECLIPSE_PLUGINS%/org.eclipse.emf.ecore.xmi_2.11.1.v20150805-0538.jar:%ECLIPSE_PLUGINS%/org.eclipse.xtext_2.8.4.v201508050135.jar:%ECLIPSE_PLUGINS%/org.eclipse.xtext.xbase.lib_2.8.4.v201508050135.jar:%ECLIPSE_PLUGINS%/com.google.inject_3.0.0.v201312141243.jar:%ECLIPSE_PLUGINS%/org.apache.log4j_1.2.15.v201012070815.jar:%ECLIPSE_PLUGINS%/javax.inject_1.0.0.v20091030.jar:%ECLIPSE_PLUGINS%/org.eclipse.xtext.util_2.8.4.v201508050135.jar:%ECLIPSE_PLUGINS%/com.google.guava_15.0.0.v201403281430.jar:%ECLIPSE_PLUGINS%/org.antlr.runtime_3.2.0.v201101311130.jar:%ECLIPSE_PLUGINS%/org.eclipse.xtext.common.types_2.8.4.v201508050135.jar:$SOSADLCLI_HOME/lib/SOSADLcli.jar:$SOSADLCLI_HOME/lib/runtime-3.0.1.jar:$SOSADLCLI_HOME/lib/SOSADLlib.jar


set CLASSPATH=%JAVA_HOME/bin:%CLASSPATH%
java -cp %CLASSPATH% org.archware.sosadl.cli.Main "$@"
