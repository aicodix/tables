
### [fixed](fixed)

Transformed and swapped lines to avoid data hazards.

### [fixed_15](fixed_15) [fixed_30](fixed_30) [fixed_45](fixed_45)

Swapped rows and columns to avoid data hazards for vector sizes of 15, 30 and 45.

### [trans](trans)

Transformed DVB LDPC code tables by [dvb_trans.cc](dvb_trans.cc)

### [trans_15](trans_15) [trans_30](trans_30) [trans_45](trans_45)

Transformed DVB LDPC code tables by [vector_trans.cc](vector_trans.cc) for vector size of 15, 30 and 45.

### [orig](orig)

Unchanged DVB LDPC parity bit address tables

DVB S2 tables copied from:
https://www.dvb.org/resources/public/standards/a83-1_dvb-s2_den302307v141.pdf

DVB S2X tables copied from:
http://www.etsi.org/deliver/etsi_en/302300_302399/30230702/01.01.01_20/en_30230702v010101a.pdf

DVB T2 tables copied from:
https://www.etsi.org/deliver/etsi_en/302700_302799/302755/01.04.01_60/en_302755v010401p.pdf

### [dvb_trans.cc](dvb_trans.cc)

Transform DVB LDPC table

### [vector_trans.cc](vector_trans.cc)

Transform DVB LDPC table for vector decoders

### [info_trans.cc](info_trans.cc)

Information about transformed table

### [comp_trans.cc](comp_trans.cc)

Compare if two transformed tables are identical

### [check_trans.cc](check_trans.cc)

Check transformed table for data hazards

### [check_vector.cc](check_vector.cc)

Check transformed vector table for data hazards

### Automatically fixing vector tables

Prerequisites:

* [Z3](https://github.com/Z3Prover/z3), [Yices](https://yices.csl.sri.com/) or [Boolector](https://boolector.github.io/) to solve [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) problems.
* A lot of patience.

Example for vector size of 15:

Copy tables that need permutation, e.g. from ```trans_15``` to ```input_15``` directory.
Run ```make solve_15``` to generate models of tables, solve models and permutate tables.
Copy solved table from ```solved_15``` directory to ```fixed_15```.
Run ```make comp_15``` to compare permuted tables in ```fixed_15``` with originals in ```trans_15```.
Run ```make check_15``` to check permuted tables in ```fixed_15``` for data hazards.
Commit new tables and send pull request.

### FYI

The following tables cant be satisfied with OVERDO enabled:

trans_45/dvb_16200_s2_c9_t2_b7.txt
trans_45/dvb_16200_s2_c7_t2_b5.txt
trans_45/dvb_16200_s2_c4_t2_b2.txt

They need to be solved with OVERDO disabled.
If ```check_vector``` reports problems, then the affected columns need to be manually rearranged to avoid data hazards.

These need about 30 GiB of RAM using BitVec and Yices:

trans_15/dvb_64800_s2_b1.txt
trans_15/dvb_64800_s2x_b1.txt
trans_15/dvb_64800_s2x_b2.txt

And these abort after more than 24 Hours, so unknown:

trans_45/dvb_16200_s2x_c5.txt
trans_45/dvb_16200_s2x_c4.txt
trans_15/dvb_64800_s2_b1.txt
trans_15/dvb_64800_s2x_b2.txt

### [model_trans.cc](model_trans.cc)

Generate model of vector table that avoids data hazards

### [solved_trans.cc](solved_trans.cc)

Generate data hazard free vector table from transformed table and solution

