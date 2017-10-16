# RTLCheck

RTLCheck is a methodology and automated tool for verifying that an RTL design
correctly implements the microarchitectural orderings and value constraints in
a microarchitectural ordering specification.

RTLCheck is derived from PipeCheck, CCICheck, COATCheck, and TriCheck.  Much of the
terminology and naming comes from those tools. See those papers/websites for
details.

http://github.com/daniellustig/pipecheck

http://github.com/ymanerka/ccicheck

http://github.com/daniellustig/coatcheck

http://github.com/ctrippel/TriCheck

### Citing RTLCheck

If you use our tool in your work, we would appreciate it if you cite our paper(s):

Daniel Lustig, Michael Pellauer, and Margaret Martonosi.  "PipeCheck:
  Specifying and Verifying Microarchitectural Enforcement of Memory Consistency
  Models", *47th International Symposium on Microarchitecture (MICRO)*,
  Cambridge UK, December 2014.

Yatin A. Manerkar, Daniel Lustig, Michael Pellauer, and Margaret Martonsi.
  "CCICheck: Using uhb Graphs to Verify the Coherence-Consistency Interface",
  *48th International Symposium on Microarchitecture (MICRO)*,
  Honolulu, HI, December 2015.

Daniel Lustig+, Geet Sethi+, Margaret Martonosi, and Abhishek Bhattacharjee.
  "COATCheck: Verifying Memory Ordering at the Hardware-OS Interface",
  *21st International Conference on Architectural Support for Programming
  Languages and Operating Systems (ASPLOS)*, Atlanta, GA, April 2016.
  (+: joint first authors)

Caroline Trippel, Yatin A. Manerkar, Daniel Lustig, Michael Pellauer,
and Margaret Martonosi. "TriCheck: Memory Model Verification at the
Trisection of Software, Hardware, and ISA", *22nd International Conference on
Architectural Support for Programming Languages and Operating Systems (ASPLOS)*,
April 2017.

Yatin A. Manerkar, Daniel Lustig, Margaret Martonosi, and Michael Pellauer.
"RTLCheck: Verifying the Memory Consistency of RTL Designs", *the 50th Annual
IEEE/ACM International Symposium on Microarchitecture (MICRO)*, October 2017.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Yatin Manerkar
at manerkar@princeton.edu, or visit our GitHub page,
github.com/ymanerka/rtlcheck.

### Status

At this point, RTLCheck is a research tool rather than an industry-strength
verification toolchain.  We do appreciate any suggestions or feedback either
in approach or in implementation.  If you are interested in any particular
feature, missing item, or implementation detail, please contact the authors and
we will try to help out as best we can.

## Building and Using RTLCheck

### Prerequisites

RTLCheck is written in Coq and extracted to OCaml for compilation to a native
executable.  RTLCheck requires OCaml (v4.0 or later) and Coq (tested on
version 8.4pl5), as well as an SVA property verifier to check its generated
properties on an RTL design. The authors have compiled and executed RTLCheck
successfully on Linux, and have proven its generated properties using the
JasperGold property verifier. Any SVA verifier should be sufficient for
checking RTLCheck's generated properties, though if you are using a verifier
other than JasperGold, you will need to configure its settings yourself.

- Coq
  - tested with Coq 8.4pl5 (October 2014)
- OCaml
  - tested with OCaml 4.01.0
- neato, part of GraphViz (only for visualization)
  - tested with 2.36.0 (20140111.2315)
- herd, part of diy (http://diy.inria.fr/herd)
  - tested with herd 5.99-D (as part of diy-5.99-D)
- SVA verifier
  - Tested with JasperGold (2015.12p002)

(all of the above except for JasperGold were tested on Ubuntu Linux)

### Building

1. `make`

## Basic Usage

The `mapping function identifier` below is a string parameter that can be used
to select a particular node and program mapping function when using RTLCheck.
To add new node and program mapping functions, you should:

1. Create a new Coq file that contains the mapping functions in the `src/`
directory (see `VscaleMappings.v` for an example of such a file).
2. Add your mapping functions file to the compilation by adding it to the
`MODULES` variable in `src/Makefile`.
3. Import the file into the FOL.v file (using a directive near the top of FOL.v
like `Require Import PipeGraph.VscaleMappings.`).
4. Select the mapping functions appropriately in the `MapNode` and
`PrintRTLAssumptions` folders according to the `rtl_map_fn` parameter, which
has a value equivalent to the `mapping function identifier` provided to RTLCheck
in the command line below.
5. Recompile the source code by running `make`.

Then you can utilise RTLCheck to generate SVA assertions and assumptions as follows:

`./src/rtlcheck -i <litmus test> -m <uspec model> -p <mapping function identifier> -t <Generated SVA properties file> [-o <generated neato graph>]`

For more options, just run `rtlcheck` by itself to see the list of available
flags.

## Working with RTL and SVA Verifiers

We have provided some scripts to ease the overhead of working with RTL verifiers like JasperGold.
The scripts are generally set up for Multi-V-scale, and will need to be modified for different RTL
designs depending on the organization of those designs.

1. If using JasperGold, we have provided Tcl script templates for both the `Hybrid` and
`Full_Proof` JasperGold configurations used in the paper, in the `scripts/rtlcheck/` directory.
(`FPV_template_hybrid.tcl` and `FPV_template_full_proof.tcl`).
The templates are currently set up for the Multi-V-scale processor used in the paper's evaluation.
If you wish to work with Multi-V-scale, its RTL source is available at http://github.com/ymanerka/multi_vscale.
You can clone it to the machine on which you will be running JasperGold,
and modify the `ROOT_PATH` variable in the Tcl script template
to point to the root directory of your Multi-V-scale repository.
If using a design other than Multi-V-scale, you should modify one of these templates to point to the
source directories and files of your RTL design. You can also change the engines used in the verification.
2.  We have also provided a template for job scripts (which add the generated SVA properties to the RTL
and run it through JasperGold) in `scripts/rtlcheck/job_template.sh`. If using Multi-V-scale, you should
modify the three variables at the top of the file to point to the tarball directory (see step 4),
the V-scale source root directory, and a directory in which to store JasperGold project
metadata (this can be anywhere) respectively. If you are using another design, you may need to modify the
job script template.
3. The `gen_props.sh` file in `scripts/rtlcheck` can automatically generate SVA properties (using RTLCheck),
Tcl scripts, and job scripts for a suite of litmus tests. The script is currently set up to work
with Multi-V-scale. If you are using another design, you will need to modify it slightly
to set the test-specific parameters in the generated files.
4. The generated SVA properties, job scripts, and Tcl scripts are packaged by `gen_props.sh` into a
tarball (which can easily be transferred to another machine if necessary). To verify
the properties for a given litmus test (assuming you have modified the scripts and templates appropriately above),
you should extract the tarball and then run the job script for that test (which is in the `jobs/`
directory of the tarball). The job script can also be passed to a SLURM scheduler to be run on a
cluster (you may need to change the parameters at the top of the job script template, depending on
how your cluster is organized and how many resources you want to allocate to the job).

## Design Approach

RTLCheck is written in Coq, a theorem prover/verification assistant.  For
example, Coq has been used to rigorously and formally verify mathematical
theorems such as the four color theorem, and it has been used to produce
C compilers which provably produce correct C code.  RTLCheck itself does not
yet contain any verified theorems or processes.  Nevertheless, we chose Coq to
make for easier integration with other formal models written using Coq, and to
leave open the possiblity of making RTLCheck more rigorous in the future.

In practice, we are also interested in using RTLCheck as a practical tool.
For this reason, we auto-extract our code from Coq to OCaml (using built-in
Coq methodology for doing so), and we compile this code to run natively.  So
far, we have not put much effort into optimizing for performance of this code,
partially because of RTLCheck's current status as a research tool, but more
importantly because we haven't yet found performance to be a bottleneck.
RTLCheck's assertion and assumption generation takes just a few seconds per test,
and the main performance bottleneck is the external JasperGold property verifier.
As such, optimization of the property generation at this point would likely be
premature anyway.

### FAQ

Q: ocamlfind: Package `js_of_ocaml.syntax' not found
A: If js_of_ocaml was installed using opam, try:
   eval `opam config env`

Q: I get a bunch of warnings like the following:
   File "Process.ml", line 39, characters 4-122:
   Warning 21: this statement never returns (or has an unsound type.)
A: This is expected behavior within the way we are using js_of_ocaml
