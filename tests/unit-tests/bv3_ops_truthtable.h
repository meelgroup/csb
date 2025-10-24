#pragma once
#include <cstdint>
#include <array>

struct BV3OpsCase {
  uint8_t x, y;
  uint8_t add, sub, mul;     // modulo-8 results
  bool add_carry;            // (x+y) >= 8
  bool sub_borrow;           // x < y (unsigned)
  bool mul_overflow;         // (x*y) >= 8
  bool ult, ule, ugt, uge;   // unsigned comparisons
  bool slt, sle, sgt, sge;   // signed (two's complement) comparisons
};

inline constexpr std::array<BV3OpsCase, 64> BV3_OPS_CASES = {{
  BV3OpsCase{ 0,  0,  0,  0,  0, false, false, false, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 0,  1,  1,  7,  0, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 0,  2,  2,  6,  0, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 0,  3,  3,  5,  0, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 0,  4,  4,  4,  0, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 0,  5,  5,  3,  0, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 0,  6,  6,  2,  0, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 0,  7,  7,  1,  0, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 1,  0,  1,  1,  0, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 1,  1,  2,  0,  1, false, false, false, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 1,  2,  3,  7,  2, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 1,  3,  4,  6,  3, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 1,  4,  5,  5,  4, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 1,  5,  6,  4,  5, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 1,  6,  7,  3,  6, false,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 1,  7,  0,  2,  7,  true,  true, false,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 2,  0,  2,  2,  0, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 2,  1,  3,  1,  2, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 2,  2,  4,  0,  4, false, false, false, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 2,  3,  5,  7,  6, false,  true, false,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 2,  4,  6,  6,  0, false,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 2,  5,  7,  5,  2, false,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 2,  6,  0,  4,  4,  true,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 2,  7,  1,  3,  6,  true,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 3,  0,  3,  3,  0, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 3,  1,  4,  2,  3, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 3,  2,  5,  1,  6, false, false, false, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 3,  3,  6,  0,  1, false, false,  true, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 3,  4,  7,  7,  4, false,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 3,  5,  0,  6,  7,  true,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 3,  6,  1,  5,  2,  true,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 3,  7,  2,  4,  5,  true,  true,  true,  true,  true, false, false, false, false,  true,  true},
  BV3OpsCase{ 4,  0,  4,  4,  0, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 4,  1,  5,  3,  4, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 4,  2,  6,  2,  0, false, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 4,  3,  7,  1,  4, false, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 4,  4,  0,  0,  0,  true, false,  true, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 4,  5,  1,  7,  4,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 4,  6,  2,  6,  0,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 4,  7,  3,  5,  4,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 5,  0,  5,  5,  0, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 5,  1,  6,  4,  5, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 5,  2,  7,  3,  2, false, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 5,  3,  0,  2,  7,  true, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 5,  4,  1,  1,  4,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 5,  5,  2,  0,  1,  true, false,  true, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 5,  6,  3,  7,  6,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 5,  7,  4,  6,  3,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 6,  0,  6,  6,  0, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 6,  1,  7,  5,  6, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 6,  2,  0,  4,  4,  true, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 6,  3,  1,  3,  2,  true, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 6,  4,  2,  2,  0,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 6,  5,  3,  1,  6,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 6,  6,  4,  0,  4,  true, false,  true, false,  true, false,  true, false,  true, false,  true},
  BV3OpsCase{ 6,  7,  5,  7,  2,  true,  true,  true,  true,  true, false, false,  true,  true, false, false},
  BV3OpsCase{ 7,  0,  7,  7,  0, false, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 7,  1,  0,  6,  7,  true, false, false, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 7,  2,  1,  5,  6,  true, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 7,  3,  2,  4,  5,  true, false,  true, false, false,  true,  true,  true,  true, false, false},
  BV3OpsCase{ 7,  4,  3,  3,  4,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 7,  5,  4,  2,  3,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 7,  6,  5,  1,  2,  true, false,  true, false, false,  true,  true, false, false,  true,  true},
  BV3OpsCase{ 7,  7,  6,  0,  1,  true, false,  true, false,  true, false,  true, false,  true, false,  true}
}};
