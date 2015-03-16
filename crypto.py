import math
import numbertheory
from numbertheory import *

####### HELPER FUNCTIONS #######

# performs the extended euclidean algorithm
# returns info to help calculate inverses
def egcd(a, b):

    x, y, u, v = 0, 1, 1, 0

    while a != 0:
        q, r = b // a, b % a
        m, n, = x - u*q, y-v*q
        b, a, x, y, u, v = a, r, u, v, m, n

    gcd = b
    
    return gcd, x, y

# returns the modular inverse of a mod m if a is coprime to m
# returns the gcd of a and m if a is not coprime to m
def modinv(a, m):

    a = a%m

    gcd, x, y = egcd(a, m)

    if gcd != 1: return False, gcd

    else: return True, x % m

# returns whether a is a quadratic residue mod something
def isQR(a, mod):

    squareList = list()

    for i in range(0, mod):
        squareList.append(i**2 % mod)

    return a in squareList

# returns a list of the quadratic residues mod something
def listQRs(mod):

    squareList = list()

    for i in range(0, mod):
        squareList.append(i**2 % mod)

    return squareList


# returns the modular square root of a number if it exists
def sqrtMod(a, mod):

    if not isQR(a, mod): return []

    answerList = list()
    singleList = list(range(0, mod))
    squareList = listQRs(mod)

    for i in range(0, mod):
        if squareList[i] == a:
            answerList.append(singleList[i])

    return answerList

# credit to martin-thoma.com
def legendre_symbol(a, p):

    if a >= p or a < 0:
        return legendre_symbol(a % p, p)
    elif a == 0 or a == 1:
        return a
    elif a == 2:
        if p%8 == 1 or p%8 == 7:
            return 1
        else:
            return -1
    elif a == p-1:
        if p%4 == 1:
            return 1
        else:
            return -1
    elif not isPrime(a):
        factors = primeFactors(a)
        product = 1
        for pi in factors:
            product *= legendre_symbol(pi, p)
        return product
    else:
        if ((p-1)/2)%2==0 or ((a-1)/2)%2==0:
            return legendre_symbol(p, a)
        else:
            return (-1)*legendre_symbol(p, a)

# returns a list of prime factors
# credit to stackoverflow.com/questions/16996217/prime-factorization-list
def primeFactors(n):

    primes = list()

    d = 2
    while d*d <= n:
        while (n%d) == 0:
            primes.append(d)
            n//=d
        d+=1

    if n>1:
        primes.append(n)

    return primes

# creates a proper set of primes involved in the prime factorization of n
# each member is a double: (base, power)
def groupPrimes(n):

    groups = list()
    primes = primeFactors(n)

    distincts = list(set(primes))

    distincts.sort()

    for i in distincts:

        temp = 0
        for j in primes:

            if j == i:
                temp += 1

        groups.append((i, temp))

    return groups

# to solve systems of congruences - credit to rosetta code
def chinese_remainder(mods, exes, lena):

    p = i = prod = 1; sm = 0

    for i in range(lena): prod *= mods[i]
    for i in range(lena):
        p = prod / mods[i]
        sm += exes[i] * modinv(p, mods[i])[1] * p
    return sm % prod

# Fermat primality test - credit to codeproject.com
def isPrime(number):

    import random
    ''' if number != 1 '''
    if (number > 1):
        ''' repeat the test few times '''
        for time in range(3):
            ''' Draw a RANDOM number in range of number ( Z_number )  '''
            randomNumber = random.randint(2, number)-1
            
            ''' Test if a^(n-1) = 1 mod n '''
            if ( pow(randomNumber, number-1, number) != 1 ):
                return False
        
        return True
    else:
        ''' case number == 1 '''
        return False  


def E_Factor(n):

    print("Factor of", n)
    if isPrime(n): 

        print(n)
        return

    point = (1,3,1)
    #curve = EllipticCurve(5, -5, n)
    curve = findB(point, 4, n)
    factor = curve.factor(point, math.ceil(math.log(n)))

    print(factor)

    if factor != False:
        E_Factor(n//factor)


def multE_Factor(b, n):

    from multiprocessing import pool

    point = (1, 2)

    for i in range(50):

        pool.apply(findB(point, 1, i, n).factor(b))


def findB(point, a, mod):

    b = 0
    while True:

        testCurve = EllipticCurve(a, b, mod)

        if testCurve.onCurve(point):

            #testCurve.printme()
            return testCurve

        b += 1

####### ELLIPTIC CURVE CLASS #######

class EllipticCurve:

    def __init__(self, a, b, mod):

        self.a = a
        self.b = b
        self.mod = mod

    def printme(self):

        print("E: y^2 = x^3 +", self.a, "x +", self.b, "( mod", self.mod, ")")


    def neg(self, point):

        if point == (0, 1, 0): return (0, 1, 0)

        return point[0], (-1 * point[1]) % self.mod, 1


    def onCurve(self, point):

        if len(point) < 3:
            print("Point must be a triple.")
            return

        if point[2] == 0: return True

        x, y = point[0], point[1]

        if y in sqrt_mod_m(x**3 + self.a*x + self.b, self.mod): 
            return True

        # if y in sqrtModP(x**3 + self.a*x + self.b, self.mod): return True

        return False 


    def add(self, point1, point2):

        if len(point1) < 3 or len(point2) < 3:
            print("Point must be a triple.")
            return

        # if not self.onCurve(point1): return False
        # if not self.onCurve(point2): return False

        # anything times the identity is itself
        if point1[2] == 0: return point2
        if point2[2] == 0: return point1

        # the identity times the identity is itself
        if point1[2] == 0 and point2[2] == 0: return (0, 1, 0)

        if point1 != point2:

            if modinv(point1[0] - point2[0], self.mod)[0] == False:
                return (0, modinv(point2[0] - point1[0], self.mod)[1], 2) 

            if point1[0] != point2[0]:

                slope = (point2[1] - point1[1]) * modinv(point2[0] - point1[0], self.mod)[1]

            else: return (0, 1, 0)

        if point1 == point2:

            if modinv((2*point1[1])%self.mod, self.mod)[0] == False: 
                return (0, modinv(2*point1[1], self.mod)[1], 2)

            slope = (3*(point1[0]**2) + self.a) * modinv(2*point1[1], self.mod)[1]          

        x3 = (slope**2 - point1[0] - point2[0]) % self.mod
        y3 = (slope * (point1[0] - x3) - point1[1]) % self.mod

        return (x3, y3, 1)


    def mult(self, point, k):

        if k == 1: return point

        sum = (0, 1, 0)

        for i in range(k):

            sum = self.add(sum, point)

        return sum

    # recursive repeated addition via doubling
    # doubles until next doubling would exceed k
    # then calls itself on the difference until 1 left
    def multP(self, point, k):

        if k == 0: return (0, 1, 0)
        if k == 1: return point

        else:

            temp = point
            doubles = 0

            while True:

                doubles += 1
                if 2**doubles >= k: 
                    doubles -= 1
                    break

                temp = self.add(temp, temp)
                if temp[2] == 2: return temp             

            leftovers = k - 2**doubles

            temp = self.add(temp, self.multP(point, leftovers))
            if temp[2] == 2: return temp

        return temp

    # this works, slowly
    def pointOrder(self, point):

        answer = (0, 1, 0)
        count = 0

        while True:

            answer = self.add(answer, point)
            #print(count, answer, test.onCurve(answer))
            count += 1
            if answer == (0, 1, 0): break      

        return count


    def bsgsGroupOrder(self, point):

        p = self.mod                            # set the constants
        m = p + 1 - math.ceil(2*(p**(1/2)))
        z = math.ceil(2*(p**(1/4)))
        m, z = int(m), int(z)
        mP = self.multP(point,m)

        babyList  = list()
        giantList  = list()
        answerList  = list()
        matchList = list()

        for i in range(z):                      # create the lists

            babyList.append(self.multP(point,i))
            giantList.append(self.neg(self.add(mP, self.multP(point,i*z))))

        for i in babyList:                      # find the matches
            for j in giantList:
                if i == j:

                    answerList.append(m + babyList.index(i) + giantList.index(j)*z)
                    matchList.append((i, j))

        for i in range(len(babyList)): print(babyList[i], "\t", giantList[i])
        print("ANSWER:")
        for i in matchList: print(i)            # print results
        return answerList


    def pohlig_hellman(self, P, Q):

        originalQ = Q
        N = self.pointOrder(P)

        factors = groupPrimes(N)        # groupPrimes() returns a list of doubles where
                                        # the first element of each double is the base
        mods = list()                   # and the second is the exponent, so we can
        exes = list()                   # refer to each as necessary

        for n in factors:

            mods.append(n[0]**n[1])

        for q in factors:               # for each component of the modulus N

            print("\n***********************")

            T = list()
            Ks = list()
            Q = originalQ               # reset Q

            e = q[1]                    # the power of the prime factor

            for j in range(q[0]):

                T.append(self.multP(P, j*(N/q[0])))     # create T list

            print("T:", T)

            for i in range(1, e+1):                     # for all elements of the base-k
                                                        # expansion of current q
                candidate = self.multP(Q, N/(q[0]**i))   
                K = T.index(candidate)                  # find the candidate in T
                Ks.append(K)                            # add to the list of ks ()
                                                        # then update Q

                Q = self.add(Q, self.neg(self.multP(P, K*q[0]**(i-1)))) 
                print("Q", i, " is", Q, "-", K, "*",q[0], "^", i-1, "*", P)

            sum = 0
            for k in Ks:                                # evaluate the expansion

                sum += k*q[0]**Ks.index(k)  
                sum %= q[0]**q[1]

            print(sum, "mod ", q[0]**q[1], "=", sum)
            exes.append(sum)                            # add it to the list

        print("\n***********************")
        print("SYSTEM:")

        print("X VALUES:\t", exes)
        print("MOD VALUES:\t", mods)

        print("ANSWER:\t\t", chinese_remainder(mods, exes, len(exes)))


    def factor(self, point, b):

        for i in range(0, b):
            #print(i)
            #print(math.factorial(i))
            temp = self.multP(point, math.factorial(i))
            #print(temp)
            if temp[2] == 2: 

                if temp[1] != self.mod:

                    return temp[1]
                    break
                    # return(temp[1])
                    #new = EllipticCurve(self.a, self.b, self.mod / temp[1])

                if temp[1] == self.mod:

                    print(temp[1], "is a trivial factor.")
                    return False

        return False
        #print("Nothing broken")





















