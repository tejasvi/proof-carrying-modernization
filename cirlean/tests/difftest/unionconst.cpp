// Union constants (run with CASES=unionconst_cases.txt): clang emits a union's
// initializer as #cir.const_record<{v : T}> : !rec_U, one value typed by the
// member it initializes (the first, or a designated one). C's meaning: that
// member is active with that value; a read of another member follows the
// union model (a scalar of the same size is reinterpreted, anything else is
// indeterminate). Global unions, local unions (copied from a constant), unions
// in structs, structs in unions, arrays of unions, a union with tail padding,
// zero initializers. Expected result (labelled per case in the cases file):
// MATCH on the c_* cases, UB from cirrun on the u_* control (native runs print
// the GCC result).

union U { int i; float f; };
union V { char c; long long l; };
struct S { int k; union U u; };
union W { struct { int a; int b; } s; long long l; };
union P { char c[5]; int i; };
union UI { int i; unsigned u; };

union U gu = {5};
union U gf = {.f = 1.5f};
union V gv = {.l = 7};
struct S gs = {1, {.f = 2.5f}};
union W gw = {{3, 4}};
union U garr[2] = {{1}, {.f = 0.5f}};
union U gz = {};
union P gp1 = {.i = 11};
union P gp2 = {{'a', 'b'}};
union UI gn = {-1};
union V gvc = {.c = 3};

// a global union, its first member
int c_global_first(int a) { return gu.i + a; }

// a global union, a designated member that is not the first
int c_global_designated(int a) { return (int)(gf.f * 2) + a; }

// a global union whose initialized member is the larger one
int c_global_larger(int a) { return (int)gv.l + a; }

// a union in a global struct
int c_struct_with_union(int a) { return gs.k * 10 + (int)(gs.u.f * 2) + a; }

// a struct in a global union
int c_union_with_struct(int a) { return gw.s.a * 10 + gw.s.b + a; }

// a global array of unions
int c_union_array(int a) { return garr[0].i * 10 + (int)(garr[1].f * 4) + a; }

// a zero-initialized global union
int c_global_zero(int a) { return gz.i + a; }

// a union with tail padding (char[5] and int: 8 bytes), each member
int c_padded(int a) { return gp1.i * 1000 + gp2.c[0] * 10 + gp2.c[1] - 'a' * 10 + a; }

// a read of another member of the same size: the constant's int reinterpreted
int c_reinterpret(int a) { return (int)(gn.u % 1000u) + a; }

// local unions copied from constants: first member, designated member
int c_local(int a) {
  union U lu = {a};
  union U lf = {.f = 3.0f};
  return lu.i * 10 + (int)lf.f;
}

// local unions in a struct, a struct in a union, an array of unions, zero
int c_local_nested(int a) {
  struct S ls = {2, {.i = a}};
  union W lw = {.l = 9};
  union U larr[2] = {{a}, {.f = 1.0f}};
  union U lz = {};
  return ls.k * 1000 + ls.u.i * 100 + (int)lw.l * 10 + larr[0].i + (int)larr[1].f + lz.i;
}

// control: a read of a larger member than the one initialized (char then long
// long: another size, so indeterminate in the union model; GCC reads the zero
// bytes of the static object)
int u_read_larger(int a) { return (int)gvc.l + a; }
