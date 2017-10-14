#!/bin/bash
# parallel job using 5 cores. and runs for 12 hours (max)
#SBATCH -N 1   # node count
#SBATCH --ntasks-per-node=4
#SBATCH -t 12:00:00
#SBATCH --mem=120G
# sends mail when process begins, and 
# when it ends. Make sure you define your email 
# address.
#SBATCH --mail-type=begin
#SBATCH --mail-type=end
#SBATCH --mail-user=<Your email address>
TARBALL_DIR=<Directory where the tarball of assertions and Tcl scripts is>
VSCALE_DIR=<Vscale root directory>
PROJ_ROOT_DIR=<JasperGold project root directory>

cd ${VSCALE_DIR}/src/main/verilog/
# Add the RTL for the test
{ head -n -1 vscale_sim_top_unmod.v; cat ${TARBALL_DIR}/sva/TEST_NAME_rtl.out; tail -n 1 vscale_sim_top_unmod.v; } > vscale_sim_top_TEST_NAME.v

# Return to Vscale root directory.
cd ../../..

# Run JasperGold.
jg -no_gui -fpv ${TARBALL_DIR}/fpv/FPV_cmdline_TEST_NAME.tcl -proj ${PROJ_ROOT_DIR}/proj_dir_TEST_NAME/|tee ${TARBALL_DIR}/jg_out/TEST_NAME.txt

# Remove the project directory.
rm -rf ${PROJ_DIR}/proj_dir_TEST_NAME/
