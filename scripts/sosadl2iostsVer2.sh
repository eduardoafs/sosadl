#!/bin/bash
#-- config start
export JAVA_HOME=/home/banchuen/jdk1.8.0_65/
export SOSADL_HOME=/home/banchuen/archware-sosadl
#-- config end

export PATH=$JAVA_HOME/bin:$PATH
java -jar $SOSADL_HOME/MainSOSADL.jar "$@"
