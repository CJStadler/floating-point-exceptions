extern int overflows;
extern int underflows;
extern int divbyzeros;
extern int invalids;

void reset_counts() {
  overflows = 0;
  underflows = 0;
  divbyzeros = 0;
  invalids = 0;
}
