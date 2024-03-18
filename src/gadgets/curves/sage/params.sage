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