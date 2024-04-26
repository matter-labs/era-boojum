# Modexp helper file.
# Note that we use w = 64 so that n = 4. 

# Montogomery constant
N = 64^(256)
mu = 2^(64) - N.inverse_mod(2^(64))
print(mu)

assert 0 <= mu < 2^(64), "mu is out of range"
assert (1 + mu * N).mod(2^(64)) == 0, "mu is incorrect"

print(f"mu = -N^(-1) mod 2^64 = 0x{mu.hex()}")

# Defining the test values
b = 0x0423423
e = 0x1234123
m = 0x32

def radix_64_representation(x: Integer):
    """
    Converts the given integer x to the radix-64 representation, that 
    is using 4 64-bit limbs.
    """

    c0 = (x >> 0) & 0xFFFFFFFFFFFFFFFF
    c1 = (x >> 64) & 0xFFFFFFFFFFFFFFFF
    c2 = (c0 >> 128) | ((c1 & 0xFFFFFFFFFFFFFFFF) << 32)
    c3 = (c1 >> 32) | ((c2 & 0xFFFFFFFFFFFFFFFF) << 32)

    return [c0, c1, c2, c3]

b_radix = radix_64_representation(b)
assert [b_radix[i] * 2**(64*i) for i in range(4)] == b


print(b.powermod(e, m))