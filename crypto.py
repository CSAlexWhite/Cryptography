import math
import numbertheory

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

# evaluates the legendre symbol given a and p
def legendre(a, p):

    if a == 0: return 0

    symbol = pow(a, int((p-1)/2), p)

    if symbol == p-1: return -1

    return symbol


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


def legendre(a, p):

    if a == 0: return 0

    ls = pow(a, int((p - 1) / 2), p)

    if ls == p - 1:
        return -1 

    else: return ls


# a faster implementation, Tonnelli-Shanks, mod a prime (credit to StackExchange)
def sqrtModP(a, p):

    a %= p

    # Simple case
    if a == 0: return [0]
    if p == 2: return [a]

    # Check solution existence on odd prime
    if legendre_symbol(a, p) != 1:
        return []

    # Simple case
    if p % 4 == 3:
        x = pow(a, (p + 1)//4, p)
        return [x, p-x]

    # Factor p-1 on the form q * 2^s (with Q odd)
    q, s = p - 1, 0
    while q % 2 == 0:
        s += 1
        q //= 2

    # Select a z which is a quadratic non resudue modulo p
    z = 1
    while legendre_symbol(z, p) != -1:
        z += 1
    c = pow(z, q, p)

    # Search for a solution
    x = pow(a, (q + 1)//2, p)
    t = pow(a, q, p)
    m = s
    while t != 1:
        # Find the lowest i such that t^(2^i) = 1
        i, e = 0, 2
        for i in range(1, m):
            if pow(t, e, p) == 1:
                break
            e *= 2

        # Update next value to iterate
        b = pow(c, int(2**(m - i - 1)), p)
        x = (x * b) % p
        t = (t * b * b) % p
        c = (b * b) % p
        m = i

    return [x, p-x]


def modular_sqrt(a, p):
    """ Find a quadratic residue (mod p) of 'a'. p
        must be an odd prime.

        Solve the congruence of the form:
            x^2 = a (mod p)
        And returns x. Note that p - x is also a root.

        0 is returned is no square root exists for
        these a and p.

        The Tonelli-Shanks algorithm is used (except
        for some simple cases in which the solution
        is known from an identity). This algorithm
        runs in polynomial time (unless the
        generalized Riemann hypothesis is false).
    """
    # Simple cases
    #
    if legendre_symbol(a, p) != 1:
        return 0
    elif a == 0:
        return 0
    elif p == 2:
        return p
    elif p % 4 == 3:
        return pow(a, int((p + 1) / 4), p)

    # Partition p-1 to s * 2^e for an odd s (i.e.
    # reduce all the powers of 2 from p-1)
    #
    s = p - 1
    e = 0
    while s % 2 == 0:
        s //= 2
        e += 1

    # Find some 'n' with a legendre symbol n|p = -1.
    # Shouldn't take long.
    #
    n = 2
    while legendre_symbol(n, p) != -1:
        n += 1

    # Here be dragons!
    # Read the paper "Square roots from 1; 24, 51,
    # 10 to Dan Shanks" by Ezra Brown for more
    # information
    #

    # x is a guess of the square root that gets better
    # with each iteration.
    # b is the "fudge factor" - by how much we're off
    # with the guess. The invariant x^2 = ab (mod p)
    # is maintained throughout the loop.
    # g is used for successive powers of n to update
    # both a and b
    # r is the exponent - decreases with each update
    #
    x = pow(a, int((s + 1) / 2), p)
    b = pow(a, s, p)
    g = pow(n, s, p)

    # x = (a**((s+1)/2))%p
    # b = (a**s)%p
    # g = (n**s)%p

    r = e

    while True:
        t = b
        m = 0
        for m in range(r):
            if t == 1:
                break
            t = pow(t, 2, p)

        if m == 0:
            return x

        gs = pow(g, 2 ** (r - m - 1), p)
        g = (gs * gs) % p
        x = (x * gs) % p
        b = (b * g) % p
        r = m


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

    if isPrime(n): 

        print(n)
        return

    point = (1,1,1)
    curve = EllipticCurve(5, -5, 455839)
    # curve = findB(point, 5, n)
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

            # testCurve.printme()
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

        if y in sqrtMod(x**3 + self.a*x + self.b, self.mod): return True

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

            if point1[0] != point2[0]:

                slope = (point2[1] - point1[1]) * modinv(point2[0] - point1[0], self.mod)[1]

            else: return (0, 1, 0)

        if point1 == point2:

            if modinv(2*point1[1], self.mod)[0] == False: 
                return (0, (modinv(2*point1[1], self.mod)[1]), 2)

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

        for i in range(b):
            #print(i)
            # print(math.factorial(i))
            temp = self.multP(point, math.factorial(i))
            #print(temp)
            if temp[2] == 2: 

                if temp[1] != self.mod:

                    #print(temp[1])
                    return(temp[1])
                    break
                    #new = EllipticCurve(self.a, self.b, self.mod / temp[1])

                if temp[1] == self.mod:

                    print(temp[1], "is a trivial factor.")
                    return False





















