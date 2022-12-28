P=21888242871839275222246405745257275088696311157297823662689037894645226208583


def split(num: int, num_bits_shift: int, length: int):
    a = []
    for _ in range(length):
        a.append( num & ((1 << num_bits_shift) - 1) )
        num = num >> num_bits_shift 
    return tuple(a)

def f(x):
    x_limbs=split(x, 64, 5)
    print(x_limbs)
    x_4=x_limbs[4]
    print("x4", x_4)
    x_3=x_limbs[3]
    q=x_4<<3 | x_3>>61

    print("q=", q, bin(q))

def p_Tbl(q):
    if 0<=q<=9:
        return q*P
    if 10<=q<=14:
        return (q-1)*P
    else:
        raise ValueError(q)

f(P//2)

