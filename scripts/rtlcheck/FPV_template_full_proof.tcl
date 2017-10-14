# ----------------------------------------
#  Copyright (C) 2014 Jasper Design Automation, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright
#  laws of the United States.
# ----------------------------------------

# Analyze design under verification files
set ROOT_PATH <Vscale root directory>
set RTL_PATH ${ROOT_PATH}/src/main/verilog/
set PROP_PATH ${ROOT_PATH}/src/main/verilog/

# Analyze property files
analyze -sv09 \
  ${PROP_PATH}/vscale_alu.v \
  ${PROP_PATH}/vscale_ctrl.v \
  ${PROP_PATH}/vscale_mul_div.v \
  ${PROP_PATH}/vscale_regfile.v \
  ${PROP_PATH}/vscale_core.v \
  ${PROP_PATH}/vscale_hasti_bridge.v \
  ${PROP_PATH}/vscale_PC_mux.v \
  ${PROP_PATH}/vscale_src_a_mux.v \
  ${PROP_PATH}/vscale_csr_file.v \
  ${PROP_PATH}/vscale_imm_gen.v \
  ${PROP_PATH}/vscale_pipeline.v \
  ${PROP_PATH}/vscale_src_b_mux.v \
  ${PROP_PATH}/vscale_arbiter.v \
  ${PROP_PATH}/vscale_dp_hasti_sram.v \
  ${PROP_PATH}/SIM_TOP_NAME

# 15 minutes for compiling properties
set_task_compile_time_limit 900
set_property_compile_time_limit 900
# Elaborate design and properties
echo "Elaboration_start: " [date +%s]
elaborate -top vscale_sim_top
echo "Elaboration_end: " [date +%s]

# Set up Clocks and Resets
echo "Reset_start: " [date +%s]
clock clk
reset reset
echo "Reset_end: " [date +%s]

# Get design information to check general complexity
echo "Design_info_start: " [date +%s]
get_design_info
echo "Design_info_end: " [date +%s]

# Check assumptions, see if we get lucky
# 1 hour max
set_prove_time_limit 1h
echo "Pass0_Start: " [date +%s]
set_max_trace_length 50
set_prove_per_property_time_limit 30s
set_prove_per_property_time_limit_factor 2
set_engine_mode {K I N C}
prove -all -covers
echo "Pass0_End: " [date +%s]
echo "ASSUMPTION_PASS_REPORT_BEGIN"
report
echo "ASSUMPTION_PASS_REPORT_END"

#
# 2nd pass: Validation of remaining properties with different engine
# 10 hours
set_prove_time_limit 10h
echo "Pass2_Start: " [date +%s]
set_max_trace_length 50
set_prove_per_property_time_limit 500s
set_prove_per_property_time_limit_factor 2
set_engine_mode {I N AD AM}
prove -all -asserts
echo "Pass2_End: " [date +%s]

# Report proof results
echo "PASS2_REPORT_BEGIN"
report
echo "PASS2_REPORT_END"
exit
