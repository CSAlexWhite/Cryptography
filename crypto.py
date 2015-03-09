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

    if not isQR(a, mod): return []

    answerList = list()
    singleList = list(range(0, mod))
    squareList = listQRs(mod)

    for i in range(0, mod):
        if squareList[i] == a:
            answerList.append(singleList[i])

    return answerList


# a faster implementation, Tonnelli-Shanks, mod a prime (credit to StackExchange)
def legendre(a, p):

    symbol = pow(a, int((p - 1)/2), p)
    if symbol == p - 1:
        return -1
    return symbol

def sqrtModP(a, p):

    a %= p

    # Simple case
    if a == 0: return [0]
    if p == 2: return [a]

    # Check solution existence on odd prime
    if legendre(a, p) != 1:
        return []

    # Simple case
    if p % 4 == 3:
        x = pow(a, int((p + 1)/4), p)
        return [x, p-x]

    # Factor p-1 on the form q * 2^s (with Q odd)
    q, s = p - 1, 0
    while q % 2 == 0:
        s += 1
        q //= 2

    # Select a z which is a quadratic non resudue modulo p
    z = 1
    while legendre(z, p) != -1:
        z += 1
    c = pow(z, q, p)

    # Search for a solution
    x = pow(a, int((q + 1)/2), p)
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
        b = pow(c, 2**(m - i - 1), p)
        x = (x * b) % p
        t = (t * b * b) % p
        c = (b * b) % p
        m = i

    return [x, p-x]


####### ELLIPTIC CURVE CLASS #######

class EllipticCurve:

    def __init__(self, a, b, mod):

        self.a = a
        self.b = b
        self.mod = mod
        print("E: y^2 = x^3 +", a, "x +", b)


    def neg(self, point):

        if point == (0, 1, 0): return (0, 1, 0)

        return point[0], (-1 * point[1]) % self.mod, 1


    def onCurve(self, point):

        if len(point) < 3:
            print("Point must be a triple.")
            return

        if point[2] == 0: return True

        x, y = point[0], point[1]

        if y in sqrtModP(x**3 + self.a*x + self.b, self.mod): return True

        return False


    def add(self, point1, point2):

        if len(point1) < 3 or len(point2) < 3:
            print("Point must be a triple.")
            return

        if not self.onCurve(point1): return False
        if not self.onCurve(point2): return False

        # anything times the identity is itself
        if point1[2] == 0: return point2
        if point2[2] == 0: return point1

        # the identity times the identity is itself
        if point1[2] == 0 and point2[2] == 0: return (0, 1, 0)

        if point1 != point2:

            if point1[0] != point2[0]:

                slope = (point2[1] - point1[1]) * modinv(point2[0] - point1[0], self.mod)

            else: return (0, 1, 0)

        if point1 == point2:

            slope = (3*(point1[0]**2) + self.a) * modinv(2*point1[1], self.mod)          

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

    # this doesn't yet
    def bsgsPointOrder(self, point):

        p = self.mod
        m = p + 1 - math.ceil(2*(p**(1/2)))
        z = math.ceil(2*(p**(1/4)))
        m, z = int(m), int(z)
        mP = self.multP(point,m)
        
        babyList = list()
        giantList = list()
        answerList = list()
        matchList = list()

        for i in range(z):

            babyList.append(self.multP(point,i))
            giantList.append(self.neg(self.add(mP, self.multP(point,i*z))))

        for i in range(z):
            for j in range(z):
                if babyList[i] == giantList[j]:
                    answerList.append(m + i + j*z)
                    matchList.append((babyList[i], giantList[i]))

        for i in matchList: print(i)

        return answerList










