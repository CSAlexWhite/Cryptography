import crypto
from crypto import *

A = LFSR((1,0,0,1,0,1,1,0,1,1,0),(11,7))

B = LFSR((1,0,0,1,1,0,0,0,0,1,0,0,1,0,1,1,1),(17, 14))

C = LFSR((0,1,0,0,1,1,1,1,1,0,1,0,1,1,0,1,1,0,1),(19,18,17,14))

def majority(a, b, c):
    
    a1 = bitwise_and(a, b)
    a2 = bitwise_and(b, c)
    a3 = bitwise_and(a, c)
    
    b1 = bitwise_or(a1, a2)
    b2 = bitwise_or(b1, a3)
    
    return b2
    

def get_majority(a, b, c, n):
    
    return majority(a.putout(n, True, False), b.putout(n, True, False), c.putout(n, True, False))
    
    