# Copyright (c) 2017-2019 Khronos Group. This work is licensed under a
# Creative Commons Attribution 4.0 International License; see
# http://creativecommons.org/licenses/by/4.0/

# Makefile to execute litmus tests
#
# foreach *.test, run litmus.exe generating the alloy inputs and "reference"
# results (SATISFIABLE/NOSOLUTION) in a temporary directory, then run alloy
# and diff the alloy output against the reference result to determine
# pass/fail.

default: runtests

litmustests = $(addsuffix .gen, $(notdir $(sort $(wildcard tests/*.test))))

build/litmus.exe : litmus.cpp
	@mkdir -p build
	g++ litmus.cpp -std=c++11 -Wall -o build/litmus.exe

Assert%: pre
	@echo "$@"
	@printf "open spirv\ncheck $@ for 8 but 1 Exec" > build/$@.als
	@echo "NOSOLUTION" > build/$@.ref
	@java -cp "org.alloytools.alloy.dist-5.0.0-20190619.101010-34.jar$(JAVACPSEPARATOR)." RunCommandLine build/$@.als > build/$@.out
	@diff --strip-trailing-cr build/$@.ref build/$@.out || echo "Test $@ failed"

asserts: AssertLocordSameLoc AssertLocordAcyclic AssertLocordComplete1 AssertLocordComplete2 AssertVisTo

# runtests is the default build target. The build include a "pre" step to
# prep, and otherwise the test executions can run in parallel with each
# other.
runtests: asserts $(litmustests)

# Create a scratch directory. Copy spirv.als there, since Alloy seems to be unable
# to open files in a relative path when running from the command line.
pre:
	@mkdir -p build
	@cp spirv.als build

clean:
	@rm -f build/*
	@!(test -d "build") || rmdir build

# Java's path separator depends on the OS. Windows is semi-colon, other OSes
# use a colon.
ifneq (,$(findstring Windows, $(OS)))
    JAVACPSEPARATOR = ;
else
    JAVACPSEPARATOR = :
endif

# Generate the temp files in ./build, run Alloy from the command line, and
# diff the generated output against the .ref file (generated from the tests)
%.test.gen : tests/%.test build/litmus.exe pre
	$(eval test = $(notdir $<))
	@echo $(test)
	@./build/litmus.exe $(test) tests build
	@java -cp "org.alloytools.alloy.dist-5.0.0-20190619.101010-34.jar$(JAVACPSEPARATOR)." RunCommandLine build/$(test).gen > build/$(test).out
	@diff --strip-trailing-cr build/$(test).ref build/$(test).out || echo "Test $@ failed"
