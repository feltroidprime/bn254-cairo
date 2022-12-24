from starkware.cairo.common.cairo_secp.bigint import BigInt3
from alt_bn128_fq2 import fq2, FQ2


struct G2Point {
    x: FQ2,
    y: FQ2,
}

struct G2JacobPoint {
    x: FQ2,
    y: FQ2,
    z: FQ2,
}


func g2() -> (res: G2Point) {
    return (
        res=G2Point(
        x=FQ2(
            e0=BigInt3(0x1edadd46debd5cd992f6ed, 0x199797111e59d0c8b53dd, 0x1800deef121f1e76426a0),
            e1=BigInt3(0x29e71297e485b7aef312c2, 0x3edcc7ed7497c6a924ccd6, 0x198e9393920d483a7260b),
            ),
        y=FQ2(
            e0=BigInt3(0x3d37b4ce6cc0166fa7daa, 0x602372d023f8f479da431, 0x12c85ea5db8c6deb4aab7),
            e1=BigInt3(0x338ef355acdadcd122975b, 0x26b5a430ce56f12cc4cdc2, 0x90689d0585ff075ec9e9),
            )
        ),
    );
}

func g2_negone() -> (res: G2Point) {
    return (
        G2Point(
        FQ2(
            BigInt3(d0=37301332318871981678327533, d1=1933688095072267321168861, d2=1813645754675075253282464),
            BigInt3(d0=50657168248156029357068994, d1=75996009454876762764004566, d2=1931027739743020521039371)),
        FQ2(
            BigInt3(d0=55568417236596615360446365, d1=20361937528170921243484528, d2=2237202444931152845658701),
            BigInt3(d0=75234859396250709295523308, d1=58200249186681967413131230, d2=2974432145097327839591194))),
    );
}

namespace g2_arithmetics {
    // formula sources : https://eprint.iacr.org/2010/526

    func to_jacobian{range_check_ptr}(x: G2Point) -> G2JacobPoint {
        let one: FQ2 = FQ2(Uint256(1, 0), Uint256(1, 0));
        let res = G2JacobPoint(x.x, x.y, one);
        return res;
    }
    func add{range_check_ptr}(x: G2JacobPoint, y: G2JacobPoint) -> G2JacobPoint {
    }

    // Algorithm 9 in paper
    func double{range_check_ptr}(a: G2JacobPoint) -> G2JacobPoint {
        // 1.
        let t0: FQ2 = fq2.mul(a.x, a.x);
        let t2: FQ2 = fq2.mul(a.z, a.z);

        // 2.
        let t1: FQ2 = fq2.add(t0, t0);
        let z3: FQ2 = fq2.mul(a.y, a.z);

        // 3.
        let t0: FQ2 = fq2.add(t0, t1);
        let t3: FQ2 = fq2.mul(a.y, a.y);

        // 4.
        let t0: FQ2 = fq2.div_by_2(t0);

        // 5.
        let t1: FQ2 = fq2.mul(t0, t2);
        let t4: FQ2 = fq2.mul(t0, a.x);

        // 6.

        // 7.
        let t1: FQ2 = fq2.mul(t3, a.x);
        // 8.

        // 9.
        let x3: FQ2 = fq2.sub(a.x, a.y);

        // 10.
        let t1: FQ2 = fq2.sub(t1, x3);

        // 11.
        let T0 = 
        // 12. 
        
        // 13. 

        let res:G2JacobPoint = G2JacobPoint(x3, y3, z3);
        return res;
    }
}
