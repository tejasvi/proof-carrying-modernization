// Vector accesses in C++ (run with CASES=vecstore_cases.txt; vecstore.c has the other cases): through a
// pointer aligned for the element but not for the vector, undefined (the conversion's value is unspecified,
// the access an aligned vector move), with a vector type aligned as float defined; to the elements of a
// library container, not modelled, undefined in cirrun (the g_ gaps) rather than a silent overwrite of the
// element the pointer designates.
#include <vector>

typedef float v4sf __attribute__ ((vector_size (16)));
typedef float v4sf_u __attribute__ ((vector_size (16), aligned (4)));

float xbuf[16];

int s_aligned_cxx(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &xbuf[4] = w;
  return (int) (xbuf[4] * 1000 + xbuf[5] * 100 + xbuf[6] * 10 + xbuf[7]) + k;
}
int s_unaligned_type_cxx(int k) {
  v4sf_u w = {1, 2, 3, 4};
  *(v4sf_u *) &xbuf[1] = w;
  return (int) (xbuf[1] * 1000 + xbuf[4]) + k;
}
int u_misaligned_cxx(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &xbuf[1] = w;
  return (int) xbuf[1] + k;
}
int u_misaligned_load_cxx(int k) {
  for (int i = 0; i < 8; ++i) xbuf[i] = (float) i;
  v4sf v = *(v4sf *) &xbuf[3];
  return (int) v[0] + k;
}

int g_container_store(int k) {
  std::vector<float> v(8, 0.0f);
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) v.data() = w;
  return (int) v[1] + k;
}
int g_container_load(int k) {
  std::vector<float> v = {1, 2, 3, 4, 5};
  v4sf x = *(v4sf *) v.data();
  return (int) (x[0] * 10 + x[3]) + k;
}
