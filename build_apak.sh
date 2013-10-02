#!/bin/sh

cd apak && make && sudo make reinstall && cd ..
cd datalog && make clean && make
make && sudo make reinstall && cd ..
cd ark && make clean && make ark && sudo make reinstall && cd ..
cd duet && make clean && make
