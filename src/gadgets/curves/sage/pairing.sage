# Twist of a curve is defined as y^2 = x^3 + b', 
# where b' is in quadratic extension of Fq[i] defined
# over irreducible polynomial x^2 + 1. Below,
# we write down the expression for b' in hex format. 
# See https://hackmd.io/@jpw/bn254 for concrete details.
re_part = Integer(19485874751759354771024239261021720505790618469301721065564631296452457478373)
im_part = Integer(266929791119991161246907387137283842545076965332900288569378510910307636690)

# Plot in hex format
print('In decimal format:')
print('re_part =', re_part)
print('im_part =', im_part)

print('\nIn hex format:')
print('re_part =', re_part.hex())
print('im_part =', im_part.hex())

# Curve parameter u and the value of [log2(u)] - 1:
u = Integer(4965661367192848881)
log2_u = N(log(u, 2))
print('\nCurve parameter u =', u)
print('log2(u) =', log2_u)
print('[log2(u)] - 1 =', floor(log2_u) - 1)
print('Binary form: ', u.binary())

# Converting in WNAF form:
def wnaf(k: Integer) -> list[Integer]:
    coefficients = []
    while k >= 1:
        if k % 2 == 1:
            k_i = 2 - (k % 4)
            k = k - k_i
            coefficients.append(k_i)
        else:
            k_i = 0
            coefficients.append(k_i)
        
        k = k // 2
    
    return coefficients

print('\nCurve in WNAF format: {}', list(reversed(wnaf(u))))

# Verifying that the decomposition is indeed correct:
u_wnaf = sum([k_i * 2**i for i, k_i in enumerate(wnaf(u))])
assert u_wnaf == u