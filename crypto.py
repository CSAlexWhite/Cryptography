import math

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

# returns the modular inverse of a mod m
def modinv(a, m):

    a = a%m

    gcd, x, y = egcd(a, m)

    if gcd != 1: return False

    else: return x % m

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

    if not isQR(a, mod): return False

    answerList = list()
    singleList = list(range(0, mod))
    squareList = listQRs(mod)

    for i in range(0, mod):
        if squareList[i] == a:
            answerList.append(singleList[i])

    return answerList


# a faster implementation, Tonnelli-Shanks, mod a prime (credit to StackExchange)
def sqrtModP(a, p):

    roots = list()

    a %= p

    if a==0: return [0]
    if p==2: return [a]

    if legendre(a, p) != 1: return roots()

    if p%4 == 3:
            x = pow(a, int((p+1)/4), p)
            return [x, p-x]

    q, s = p-1, 0
    while q%2 == 0:
        s += 1
        q //=2

    z = 1
    while legendre(z, p) != -1:
        z += 1
    c = pow(z, int(q), p)

    x = pow(a, int((q+1)/2), p)
    t = pow(a, int(q), p)
    m = s

    while t != 1:

        i, e = 0, 2

        for i in xrange(1, m):
            if pow(t, e, p) == 1:
                break
            e *= 2

        b = pow(int(c), int(2**(m-i-1)), p)
        x = (x*b)%p
        t = (t*b*b)%p
        c = (b*b)*p
        m = i

    return [x, p-x]




####### ELLIPTIC CURVE CLASS #######

class EllipticCurve:

    def __init__(self, a, b, mod):

        self.a = a
        self.b = b
        self.mod = mod

    def onCurve(point):

        if y in sqrtMod(x**3 + a*x + b, mod): return True

        return False

    def add(point1, point2):

        if not onCurve(point1): return False
        if not onCurve(point2): return False

        if point1 == point2:
            slope = (3*[point1[0] + a]) * modinv(2*point1[1])

        else:
            slope = (point2[1] - point1[1]) * modinv(point2[0] - point1[0])

        x3 = slope**2 - point1[0] - point2[0]
        y3 = slope * (point1[0] - x3) - point1[1]

        return (x3, y3)

    # def mult(point, k):

    #   if k == 1: return point

    #   else:




