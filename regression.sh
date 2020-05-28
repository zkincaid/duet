#!/bin/bash

# Run a set of regression tests.
# Command line arguments
#   run              Run the suite of regression tests
#   run <set>        Run a particular set of regression tests
#   baselines        Generate baselines for all regression tests
#   baselines <set>  Generate a particular set of regression tests
#   sets             Get a list of all baseline sets

DIR=`dirname $0`
REGRESSION_DIR="$DIR/regression"
REGRESSION_TXT="$REGRESSION_DIR/regression.txt"
RUN_MAIN="$DIR/duet.exe"
WORKING="$REGRESSION_DIR/.working"

phase () {
    NAME=$1
    NAME_LENGTH=`echo $NAME | wc -c`
    PADDING=`yes - | head -$((75 - $NAME_LENGTH)) | tr -d '\n'`
    echo ---- $NAME $PADDING
}

run_all () {
    FAMILY=$1
    FAMILY_DIR=$REGRESSION_DIR/$FAMILY
    PASSED=0
    FAILED=0
    phase $FAMILY regression tests

    while read x; do
	TEST=`echo $x | sed 's/\([^:]*\):.*/\1/'`
	COMMAND=`echo $x | sed 's/[^:]*: \(.*\)/\1/' | sed "s#@code#$FAMILY_DIR/code#g"`

	WORKING_FAM_DIR="$WORKING/$FAMILY"
	if [ ! -d $WORKING_FAM_DIR ]; then
	    echo Make $WORKING_FAM_DIR
	    mkdir $WORKING_FAM_DIR
	fi
	echo Running $TEST...
	WORKING_OUTPUT="$WORKING_FAM_DIR/$TEST.working"
	BASELINE="$FAMILY_DIR/baselines/$TEST.baseline"
	$DIR/$COMMAND > $WORKING_OUTPUT
	DIFF_COUNT=`diff $BASELINE $WORKING_OUTPUT | wc -l`
	if [ $DIFF_COUNT -gt 0 ]; then
	    echo Baseline differs!
	    diff $BASELINE $WORKING_OUTPUT > $WORKING_FAM_DIR/$TEST.diff
	    cat $WORKING_FAM_DIR/$TEST.diff
	    FAILED=$(($FAILED+1))
	else
	    PASSED=$(($PASSED+1))
	fi
    done < <(cat $FAMILY_DIR/regression.txt | grep -v "#")
    echo "Passed: $PASSED"
    echo "Failed: $FAILED"
}

regression_sets () {
    cd $REGRESSION_DIR && ls -d */ | sed s#/##
}

generate_all () {
    FAMILY=$1
    FAMILY_DIR=$REGRESSION_DIR/$FAMILY
    phase $FAMILY baselines

    while read x; do
	TEST=`echo $x | sed 's/\([^:]*\):.*/\1/'`
	COMMAND=`echo $x | sed 's/[^:]*: \(.*\)/\1/' | sed "s#@code#$FAMILY_DIR/code#g"`
	echo Generating $TEST...

        $DIR/$COMMAND > $FAMILY_DIR/baselines/$TEST.baseline
    done < <(cat $FAMILY_DIR/regression.txt | grep -v "#")
}

if [ $# -lt 1 ]; then
    FLAG=run
else
    FLAG=$1
fi
shift
if [ $# -lt 1 ]; then
    SETS=`regression_sets`
else
    SETS=$@
fi


case $FLAG in
    "run")
	echo Running regression tests...
	rm -rf $WORKING
	mkdir $WORKING

	for s in $SETS; do
	    run_all $s
	done
	;;
    "baselines")
	echo Generating baselines...

	for s in $SETS; do
	    generate_all $s
	done
	;;
    "sets")
	echo Regression test sets:
	regression_sets
	;;
    *)
	echo Command $FLAG not found
	;;
esac
