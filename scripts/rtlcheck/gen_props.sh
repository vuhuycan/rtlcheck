#!/bin/bash

rm -rf pc_out/*
rm -rf sva/*
rm -rf jobs/*
rm -rf fpv/*
rm -rf jg_out/*

mkdir -p pc_out/
mkdir -p sva/
mkdir -p jobs/
mkdir -p fpv/
mkdir -p jg_out/

for file in $(find "../../tests/rtlcheck/SC/" -maxdepth 1 -name \*.test); do
    file_chop=$(basename $file)
    file_chop="${file_chop%.*}"
    echo "Running test $file_chop"
    ../../src/rtlcheck -v 7 -i $file -o pc_out/$file_chop.out \
    -m ../../uarches/Vscale.uarch -t sva/${file_chop}_rtl.out
    sed -e "s/TEST_NAME/${file_chop}/g" job_template.sh > jobs/job_${file_chop}.sh
    sed -e "s/SIM_TOP_NAME/vscale_sim_top_${file_chop}.v/g" FPV_template_full_proof.tcl > fpv/FPV_cmdline_${file_chop}.tcl
done

rm -rf rtlcheck_tarball.tgz
tar czvf rtlcheck_tarball.tgz fpv/ jg_out/ jobs/ pc_out/ sva/
