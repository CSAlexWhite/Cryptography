# -*- coding: utf-8 -*-
"""
Created on Fri Apr 24 11:40:15 2015
Python3
@author: Alex
"""

#def lfsr(seed, taps):
#    
#    import time
#    sr = seed
#    xor = 0
#    
#    
#    
#    while 1:
#        
#        for t in taps:          
#            xor += int(sr[t])
#            
#        if xor%2 == 0.0:
#            xor = 0
#            
#        else:
#            xor = 1
#            
#    print(xor)
#    time.sleep(0.75)
#    sr, xor = str(xor) + sr[:-1], 0
#    print(sr)
#    print()
#    time.sleep(0.75)
    
    
def lfsr(fill, taps, steps):

    output = list()
    register = list()     # the register is initialized as the size of the queue
    
    for i in fill:        # initialize the register with the fill
        
        register.append(fill[i])
    
    next = 0
    for step in range(steps):
        
        next = xor(register, taps)        
        output.append(register[0])
        #print(register)
        register.pop(0)
        register.append(next)
        
    print(output)
               
        
def xor(fill, taps):
    
    sum = 0
    for i in taps:
        
        sum += fill[i]
    
    sum %= 2
    
    return sum
    
    
    
    
    
    






    

    
    
    
    
    