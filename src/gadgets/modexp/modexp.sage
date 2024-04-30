# Modexp helper file.
# Note that we use w = 64 so that n = 4. 

base = 0x123456789abcdef
exponent = 0x123456789abcdef
modulus = 3564

MAX_BITS = 512

def div(base: Integer, modulus: Integer) -> Integer:
    # Extend binary form of base to MAX_BITS
    base = base.binary()
    base = base.zfill(MAX_BITS)
    print(base)

    #print(base.binary())
    #print(modulus.binary())

div(base, modulus)

#assert find_modulus(base, modulus) == base % modulus

