from starkware.cairo.common.uint256 import Uint256
from starkware.cairo.common.math_cmp import is_le

from src.curve import P_low, P_high

const SHIFT = 2 ** 128;
const ALL_ONES = 2 ** 128 - 1;
const ALL_ONES_127 = 2 ** 127 - 1;
const HALF_SHIFT = 2 ** 64;
const UPPER_BOUND = 2 ** 224;
const HIGH_BOUND = UPPER_BOUND / SHIFT;

// Represents an integer in the range [0, 2^384).
struct Uint384 {
    // The low 128 bits of the value.
    d0: felt,
    // The middle 128 bits of the value.
    d1: felt,
    // The # 128 bits of the value.
    d2: felt,
}

struct Uint512 {
    d0: felt,
    d1: felt,
    d2: felt,
    d3: felt,
}
struct Uint768 {
    d0: felt,
    d1: felt,
    d2: felt,
    d3: felt,
    d4: felt,
    d5: felt,
}

namespace u255 {
    // Verifies that the given integer is valid.
    func check{range_check_ptr}(a: Uint256) {
        // tempvar h = a.high - 2 ** 127;
        [range_check_ptr] = a.low;
        [range_check_ptr + 1] = a.high;
        let range_check_ptr = range_check_ptr + 2;
        return ();
    }

    // Assume a and b are lower than 2**255-19
    func add{range_check_ptr}(a: Uint256, b: Uint256) -> Uint256 {
        alloc_locals;
        local res: Uint256;
        local carry_low: felt;
        %{
            sum_low = ids.a.low + ids.b.low
            ids.carry_low = 1 if sum_low >= ids.SHIFT else 0
        %}
        // changed hint, no carry_high
        assert carry_low * carry_low = carry_low;
        // assert carry_low = 0;

        assert res.low = a.low + b.low - carry_low * SHIFT;
        assert res.high = a.high + b.high + carry_low;
        // check(res);

        return res;
    }

    func add_carry{range_check_ptr}(a: Uint256, b: Uint256) -> (res: Uint256, carry: felt) {
        alloc_locals;
        local res: Uint256;
        local carry_low: felt;
        local carry_high: felt;
        %{
            sum_low = ids.a.low + ids.b.low
            ids.carry_low = 1 if sum_low >= ids.SHIFT else 0
            sum_high = ids.a.high + ids.b.high + ids.carry_low
            ids.carry_high = 1 if sum_high >= ids.SHIFT else 0
        %}

        assert carry_low * carry_low = carry_low;
        assert carry_high * carry_high = carry_high;

        assert res.low = a.low + b.low - carry_low * SHIFT;
        assert res.high = a.high + b.high + carry_low - carry_high * SHIFT;
        check(res);

        return (res, carry_high);
    }
    func add_u512_and_u256{range_check_ptr}(a: Uint512, b: Uint256) -> Uint512 {
        alloc_locals;

        let a_low = Uint256(low=a.d0, high=a.d1);
        let a_high = Uint256(low=a.d2, high=a.d3);

        let (sum_low, carry0) = add_carry(a_low, b);

        local res: Uint512;

        res.d0 = sum_low.low;
        res.d1 = sum_low.high;
        // res.d2 = sum_low.d2;

        // TODO : create add_one (high bits not needed)
        let a_high_plus_carry = add(a_high, Uint256(carry0, 0));

        res.d2 = a_high_plus_carry.low;
        res.d3 = a_high_plus_carry.high;

        return res;
    }
    func add_u768_and_u256{range_check_ptr}(a: Uint768, b: Uint256) -> (res: Uint768, carry: felt) {
        alloc_locals;

        let a_low = Uint256(a.d0, a.d1);
        let a_mid = Uint256(a.d2, a.d3);
        let a_high = Uint256(a.d4, a.d5);

        let (sum_low, carry0) = add_carry(Uint256(a.d0, a.d1), b);

        local res: Uint768;

        res.d0 = sum_low.low;
        res.d1 = sum_low.high;

        // TODO : create add_one (high bits not needed)
        let (a_mid_plus_carry, carry1) = add_carry(a_mid, Uint256(carry0, 0));

        res.d2 = a_mid_plus_carry.low;
        res.d3 = a_mid_plus_carry.high;

        let (a_high_plus_carry, carry2) = add_carry(a_high, Uint256(carry1, 0));

        res.d4 = a_high_plus_carry.low;
        res.d5 = a_high_plus_carry.high;

        return (res, carry2);
    }
    func mul{range_check_ptr}(a: Uint256, b: Uint256) -> Uint512 {
        alloc_locals;
        let (a0, a1) = split_64(a.low);
        let (a2, a3) = split_64(a.high);
        let (b0, b1) = split_64(b.low);
        let (b2, b3) = split_64(b.high);

        local B0 = b0 * HALF_SHIFT;
        local b12 = b1 + b2 * HALF_SHIFT;

        let (res0, carry) = split_128(a1 * B0 + a0 * b.low);
        let (res2, carry) = split_128(a3 * B0 + a2 * b.low + a1 * b12 + a0 * b.high + carry);
        let (res4, carry) = split_128(a3 * b12 + a2 * b.high + a1 * b3 + carry);
        let res = Uint512(res0, res2, res4, a3 * b3 + carry);
        return res;
    }
    func square{range_check_ptr}(a: Uint256) -> Uint512 {
        alloc_locals;
        let (a0, a1) = split_64(a.low);
        let (a2, a3) = split_64(a.high);

        const HALF_SHIFT2 = 2 * HALF_SHIFT;
        // local A0 = a0 * HALF_SHIFT2;
        // local ad0_2 = a.low * 2;
        local a12 = a1 + a2 * HALF_SHIFT2;

        let (res0, carry) = split_128(a0 * (a0 + a1 * HALF_SHIFT2));
        let (res2, carry) = split_128(a0 * a.high * 2 + a1 * a12 + carry);
        let (res4, carry) = split_128(a3 * (a1 + a12) + a2 * a2 + carry);

        let res = Uint512(res0, res2, res4, a3 * a3 + carry);
        return res;
    }

    func mul2ab{range_check_ptr}(a: Uint256, b: Uint256) -> Uint512 {
        alloc_locals;
        let (a0, a1) = split_64_2(a.low);
        let (a2, a3) = split_64_2(a.high);
        let (b0, b1) = split_64(b.low);
        let (b2, b3) = split_64(b.high);
        local B0 = b0 * HALF_SHIFT;  // + 2 ** 65;
        local b12 = b1 + b2 * HALF_SHIFT;

        let (res0, carry) = split_128(a1 * B0 + a0 * b.low);
        let (res2, carry) = split_128(a3 * B0 + a2 * b.low + a1 * b12 + a0 * b.high + carry);
        let (res4, carry) = split_128(a3 * b12 + a2 * b.high + a1 * b3 + carry);
        let (res6, carry) = split_128(a3 * b3 + carry);
        assert carry = 0;
        let res = Uint512(res0, res2, res4, res6);
        return res;
    }
    // Multiply by 2
    func double_u255{range_check_ptr}(a: Uint256) -> Uint256 {
        alloc_locals;
        let (a0, a1) = split_64(a.low);
        let (a2, a3) = split_64(a.high);
        local b0 = 2 ** 65;
        let (res0, carry) = split_128(a1 * b0 + 2 * a0);
        // assert carry = 0;
        let (res2, carry) = split_128(a3 * b0 + 2 * a2 + carry);

        assert carry = 0;
        let res = Uint256(res0, res2);
        return res;
    }
    func double_u511{range_check_ptr}(a: Uint512) -> Uint512 {
        alloc_locals;
        let (a0, a1) = split_64(a.d0);
        let (a2, a3) = split_64(a.d1);
        let (a4, a5) = split_64(a.d2);
        let (a6, a7) = split_64(a.d3);

        local B0 = 2 * HALF_SHIFT;

        let (res0, carry) = split_128(a1 * B0 + a0 * 2);
        let (res2, carry) = split_128(a3 * B0 + a2 * 2 + carry);
        let (res4, carry) = split_128(a5 * B0 + a4 * 2 + carry);
        let (res6, carry) = split_128(a7 * B0 + a6 * 2 + carry);
        assert carry = 0;
        let res = Uint512(d0=res0, d1=res2, d2=res4, d3=res6);
        return res;
    }
    func mul_u512_by_u256{range_check_ptr}(a: Uint512, b: Uint256) -> Uint768 {
        alloc_locals;
        let (a0, a1) = split_64(a.d0);
        let (a2, a3) = split_64(a.d1);
        let (a4, a5) = split_64(a.d2);
        let (a6, a7) = split_64(a.d3);

        let (b0, b1) = split_64(b.low);
        let (b2, b3) = split_64(b.high);

        local B0 = b0 * HALF_SHIFT;
        local b12 = b1 + b2 * HALF_SHIFT;

        let (res0, carry) = split_128(a1 * B0 + a0 * b.low);
        let (res2, carry) = split_128(a3 * B0 + a2 * b.low + a1 * b12 + a0 * b.high + carry);
        let (res4, carry) = split_128(
            a5 * B0 + a4 * b.low + a3 * b12 + a2 * b.high + a1 * b3 + carry
        );
        let (res6, carry) = split_128(
            a7 * B0 + a6 * b.low + a5 * b12 + a4 * b.high + a3 * b3 + carry
        );
        let (res8, carry) = split_128(a7 * b12 + a6 * b.high + a5 * b3 + carry);
        let (res10, carry) = split_128(a7 * b3 + carry);
        let res = Uint768(d0=res0, d1=res2, d2=res4, d3=res6, d4=res8, d5=res10);
        return res;
    }

    func u768_modulo_p_25519{range_check_ptr}(a: Uint768) -> Uint256 {
        alloc_locals;
        local quotient: Uint768;
        local remainder: Uint384;
        // tempvar a = Uint768(x.d0, x.d1, x.d2, x.d3, 0, 0);
        tempvar div = Uint384(P_low, P_high, 0);
        tempvar p = Uint256(P_low, P_high);
        %{
            def split(num: int, num_bits_shift: int, length: int):
                a = []
                for _ in range(length):
                    a.append( num & ((1 << num_bits_shift) - 1) )
                    num = num >> num_bits_shift 
                return tuple(a)

            def pack(z, num_bits_shift: int) -> int:
                limbs = (z.d0, z.d1, z.d2)
                return sum(limb << (num_bits_shift * i) for i, limb in enumerate(limbs))
                
            def pack_extended(z, num_bits_shift: int) -> int:
                limbs = (z.d0, z.d1, z.d2, z.d3, z.d4, z.d5)
                return sum(limb << (num_bits_shift * i) for i, limb in enumerate(limbs))

            a = pack_extended(ids.a, num_bits_shift = 128)
            div = pack(ids.div, num_bits_shift = 128)

            quotient, remainder = divmod(a, div)

            quotient_split = split(quotient, num_bits_shift=128, length=6)

            ids.quotient.d0 = quotient_split[0]
            ids.quotient.d1 = quotient_split[1]
            ids.quotient.d2 = quotient_split[2]
            ids.quotient.d3 = quotient_split[3]
            ids.quotient.d4 = quotient_split[4]
            ids.quotient.d5 = quotient_split[5]

            remainder_split = split(remainder, num_bits_shift=128, length=3)
            ids.remainder.d0 = remainder_split[0]
            ids.remainder.d1 = remainder_split[1]
            ids.remainder.d2 = remainder_split[2]
        %}
        assert quotient.d4 = 0;
        assert quotient.d5 = 0;
        let res_mul: Uint768 = mul_u512_by_u256(
            Uint512(quotient.d0, quotient.d1, quotient.d2, quotient.d3), p
        );

        tempvar res_remainder = Uint256(remainder.d0, remainder.d1);
        let (check_val: Uint768, add_carry) = add_u768_and_u256(res_mul, res_remainder);

        assert add_carry = 0;
        assert check_val = a;

        let is_valid = lt(res_remainder, p);
        assert is_valid = 1;

        return res_remainder;
    }
    func u768_div_u384{range_check_ptr}(a: Uint768, div: Uint384) -> Uint384 {
        alloc_locals;
        local quotient: Uint768;
        local remainder: Uint384;
        // tempvar a = Uint768(x.d0, x.d1, x.d2, x.d3, 0, 0);
        tempvar div = Uint384(P_low, P_high, 0);
        tempvar p = Uint256(P_low, P_high);
        %{
            def split(num: int, num_bits_shift: int, length: int):
                a = []
                for _ in range(length):
                    a.append( num & ((1 << num_bits_shift) - 1) )
                    num = num >> num_bits_shift 
                return tuple(a)

            def pack(z, num_bits_shift: int) -> int:
                limbs = (z.d0, z.d1, z.d2)
                return sum(limb << (num_bits_shift * i) for i, limb in enumerate(limbs))
                
            def pack_extended(z, num_bits_shift: int) -> int:
                limbs = (z.d0, z.d1, z.d2, z.d3, z.d4, z.d5)
                return sum(limb << (num_bits_shift * i) for i, limb in enumerate(limbs))

            a = pack_extended(ids.a, num_bits_shift = 128)
            div = pack(ids.div, num_bits_shift = 128)

            quotient, remainder = divmod(a, div)

            quotient_split = split(quotient, num_bits_shift=128, length=6)

            ids.quotient.d0 = quotient_split[0]
            ids.quotient.d1 = quotient_split[1]
            ids.quotient.d2 = quotient_split[2]
            ids.quotient.d3 = quotient_split[3]
            ids.quotient.d4 = quotient_split[4]
            ids.quotient.d5 = quotient_split[5]

            remainder_split = split(remainder, num_bits_shift=128, length=3)
            ids.remainder.d0 = remainder_split[0]
            ids.remainder.d1 = remainder_split[1]
            ids.remainder.d2 = remainder_split[2]
        %}
        assert quotient.d4 = 0;
        assert quotient.d5 = 0;
        let res_mul: Uint768 = mul_u512_by_u256(
            Uint512(quotient.d0, quotient.d1, quotient.d2, quotient.d3), p
        );

        tempvar res_remainder = Uint384(remainder.d0, remainder.d1, res_remainder.d2);
        let (check_val: Uint768, add_carry) = add_u768_and_u256(res_mul, res_remainder);

        assert add_carry = 0;
        assert check_val = a;

        let is_valid = lt(res_remainder, p);
        assert is_valid = 1;

        return res_remainder;
    }
    func a_modulo_bn254p{range_check_ptr}(a: Uint256) -> Uint256 {
        alloc_locals;
        // Guess the quotient and the remainder.
        local quotient: Uint256;
        local remainder: Uint256;
        tempvar div = Uint256(P_low, P_high);
        %{
            a = (ids.a.high << 128) + ids.a.low
            div = (ids.div.high << 128) + ids.div.low
            quotient, remainder = divmod(a, div)

            ids.quotient.low = quotient & ((1 << 128) - 1)
            ids.quotient.high = quotient >> 128
            ids.remainder.low = remainder & ((1 << 128) - 1)
            ids.remainder.high = remainder >> 128
        %}
        // these are in starkware lib, but not in uint 384, are they really necessary ? :
        // uint256_check(quotient);
        // uint256_check(remainder);
        let res_mul: Uint512 = mul(quotient, div);
        assert res_mul.d2 = 0;
        assert res_mul.d3 = 0;
        let check_val: Uint256 = add(Uint256(res_mul.d0, res_mul.d1), remainder);
        assert check_val = a;

        let is_valid = lt(remainder, div);
        assert is_valid = 1;
        return remainder;
    }

    func modulo_2{range_check_ptr}(a: Uint256) -> (quotient: Uint256, remainder: felt) {
        alloc_locals;
        local div: Uint256 = Uint256(2, 0);

        // Guess the quotient and the remainder.
        local quotient: Uint256;
        local remainder: Uint256;
        %{
            a = (ids.a.high << 128) + ids.a.low
            div = (ids.div.high << 128) + ids.div.low
            quotient, remainder = divmod(a, div)

            ids.quotient.low = quotient & ((1 << 128) - 1)
            ids.quotient.high = quotient >> 128
            ids.remainder.low = remainder & ((1 << 128) - 1)
            ids.remainder.high = remainder >> 128
        %}
        check(quotient);
        check(remainder);

        let res_mul: Uint256 = double_u255(quotient);

        let check_val = add(res_mul, remainder);
        assert check_val = a;

        let is_valid = lt(remainder, div);
        assert is_valid = 1;

        return (quotient, remainder.low);
    }

    func unsigned_div_rem{range_check_ptr}(a: Uint256, div: Uint256) -> (
        quotient: Uint256, remainder: Uint256
    ) {
        alloc_locals;

        // If div == 0, return (0, 0).
        if (div.low + div.high == 0) {
            return (quotient=Uint256(0, 0), remainder=Uint256(0, 0));
        }

        // Guess the quotient and the remainder.
        local quotient: Uint256;
        local remainder: Uint256;
        %{
            a = (ids.a.high << 128) + ids.a.low
            div = (ids.div.high << 128) + ids.div.low
            quotient, remainder = divmod(a, div)

            ids.quotient.low = quotient & ((1 << 128) - 1)
            ids.quotient.high = quotient >> 128
            ids.remainder.low = remainder & ((1 << 128) - 1)
            ids.remainder.high = remainder >> 128
        %}
        check(quotient);
        check(remainder);

        let res_mul: Uint512 = mul(quotient, div);
        assert res_mul.d2 = 0;
        assert res_mul.d3 = 0;
        let check_val = add(Uint256(res_mul.d0, res_mul.d1), remainder);
        assert check_val = a;

        let is_valid = lt(remainder, div);
        assert is_valid = 1;
        return (quotient=quotient, remainder=remainder);
    }
    // Returns the bitwise NOT of an integer.
    func not{range_check_ptr}(a: Uint256) -> (res: Uint256) {
        return (res=Uint256(low=ALL_ONES - a.low, high=ALL_ONES - a.high));
    }
    // Returns the negation of an integer.
    // Note that the negation of -2**255 is -2**255.
    // Computes 2**256-a
    func neg{range_check_ptr}(a: Uint256) -> Uint256 {
        let (not_num) = not(a);
        let res = add(not_num, Uint256(low=1, high=0));
        return res;
    }
    // Subtracts two integers. Returns the result as a 256-bit integer.
    func sub{range_check_ptr}(a: Uint256, b: Uint256) -> Uint256 {
        alloc_locals;

        let b_neg = neg(b);
        let res = add(a, b_neg);

        %{ print_sub(ids.a, 'a', ids.b, 'b', ids.res, 'res') %}

        return res;
    }
    //
    // func super_sub{range_check_ptr}(a: Uint256, b: Uint256) -> Uint256 {
    //     alloc_locals;

    // let b_neg = neg(b);
    //     let res = add(a, b_neg);
    //     // begin

    // let le = lt(b, a);

    // local Ya_min_Xa: Uint256;

    // if (le == 0) {
    //         let uiu = a_modulo_2_255_19(res);
    //         assert Ya_min_Xa.low = uiu.low;
    //         assert Ya_min_Xa.high = uiu.high;
    //         tempvar range_check_ptr = range_check_ptr;
    //         //
    //     } else {
    //         assert Ya_min_Xa.low = res.low;
    //         assert Ya_min_Xa.high = res.high - 2 ** 128;
    //         tempvar range_check_ptr = range_check_ptr;
    //     }
    //     // %{ print_u_256_info(ids.Ya_min_Xa, 'Ya_min_xa') %}

    // // end
    //     return Ya_min_Xa;
    // }
    func eq{range_check_ptr}(a: Uint256, b: Uint256) -> felt {
        // Checks low first.
        if (a.low != b.low) {
            return 0;
        }
        if (a.high != b.high) {
            return 0;
        }
        return 1;
    }
    func split_64{range_check_ptr}(a: felt) -> (low: felt, high: felt) {
        alloc_locals;
        local low: felt;
        local high: felt;

        %{
            ids.low = ids.a & ((1<<64) - 1)
            ids.high = ids.a >> 64
        %}
        assert a = low + high * HALF_SHIFT;
        // assert [range_check_ptr + 0] = low;
        // assert [range_check_ptr + 1] = HALF_SHIFT - 1 - low;
        // assert [range_check_ptr + 2] = high;
        // let range_check_ptr = range_check_ptr + 3;
        return (low, high);
    }
    func split_64_2{range_check_ptr}(a: felt) -> (low: felt, high: felt) {
        alloc_locals;
        local low: felt;
        local high: felt;

        %{
            ids.low = ids.a & ((1<<64) - 1)
            ids.high = ids.a >> 64
        %}
        assert a = low + high * HALF_SHIFT;
        assert [range_check_ptr + 0] = low;
        assert [range_check_ptr + 1] = HALF_SHIFT - 1 - low;
        assert [range_check_ptr + 2] = high;
        let range_check_ptr = range_check_ptr + 3;
        return (2 * low, 2 * high);
    }
    // Splits a field element in the range [0, 2^224) to its low 128-bit and high 96-bit parts.
    func split_128{range_check_ptr}(a: felt) -> (low: felt, high: felt) {
        alloc_locals;
        local low: felt;
        local high: felt;

        %{
            ids.low = ids.a & ((1<<128) - 1)
            ids.high = ids.a >> 128
        %}
        assert a = low + high * SHIFT;  // SHIFT = 2**128
        assert [range_check_ptr + 0] = high;
        assert [range_check_ptr + 1] = HIGH_BOUND - 1 - high;
        assert [range_check_ptr + 2] = low;
        let range_check_ptr = range_check_ptr + 3;
        return (low, high);
    }
    func lt{range_check_ptr}(a: Uint256, b: Uint256) -> felt {
        if (a.high == b.high) {
            return is_le(a.low + 1, b.low);
        }
        return is_le(a.high + 1, b.high);
    }
}
