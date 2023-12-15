#!/bin/sh
# Shell script to test some verification examples

# Check differences:
check_diff() {
  OUTFILE=$1
  RESULTFILE=$2
  DIFF=diff$$
  diff $RESULTFILE $OUTFILE > $DIFF
  if [ "`cat $DIFF`" = "" ] ; then
    echo
    echo "Regression test successfully executed!"
    /bin/rm -f $OUTFILE $DIFF
  else
    echo
    echo "Differences in regression test occurred:"
    cat $DIFF
    /bin/rm -f $DIFF
    /bin/mv -f $OUTFILE LOGFILE
    echo "Test output saved in file 'LOGFILE'."
    exit 1
  fi
}

LOGFILE=xxx$$
# System libraries to be precompiled before testing:
COMPILELIBS="Control.Search.Unsafe Control.Search.SetFunctions"
# System libraries to be tested:
TESTLIBS="Prelude Data.Maybe Data.List"
# Example programs to be tested:
TESTPROGS="ArithDiv DataList DepthkDomain EncapSearch Equality InfLists InferCallTypes Risers SetFuns Split TestSuccess"

# Testing standard (top constructor) domain:
TOOL="curry-calltypes"

$TOOL -q $COMPILELIBS
$TOOL -r -q $TESTLIBS | tee $LOGFILE
check_diff $LOGFILE RESULTLIBS.txt
$TOOL -r -q $TESTPROGS | tee $LOGFILE
check_diff $LOGFILE RESULTEXAMPLES.txt


# Testing depth-2 domain:
TOOL="curry-calltypes-values2"

$TOOL -q $COMPILELIBS
$TOOL -r -q $TESTLIBS | tee $LOGFILE
check_diff $LOGFILE RESULTLIBS_VALUES2.txt
$TOOL -r -q $TESTPROGS | tee $LOGFILE
check_diff $LOGFILE RESULTEXAMPLES_VALUES2.txt
