
### [fixed](fixed)

Transformed and manually swapped lines to avoid data hazards.

### [trans](trans)

Transformed DVB LDPC code tables by [dvb_trans.cc](dvb_trans.cc)

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

### [info_trans.cc](info_trans.cc)

Information about transformed table

### [check_trans.cc](check_trans.cc)

Check transformed table for data hazards

