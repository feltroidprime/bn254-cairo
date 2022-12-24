from starkware.cairo.common.cairo_secp.bigint import (
    BigInt3,
    nondet_bigint3,
    bigint_mul,
    UnreducedBigInt5,
)
from src.curve import P0, P1, P2

from alt_bn128_g1 import G1Point, compute_doubling_slope, compute_slope
from alt_bn128_g2 import G2Point
from alt_bn128_gt import (
    GTPoint,
    gt_slope,
    gt_doubling_slope,
    twist,
    g1_to_gt,
    fq12_mul,
    gt_double,
    gt_add,
)

const ate_loop_count = 29793968203157093288;
const log_ate_loop_count = 63;

from starkware.cairo.common.registers import get_label_location
