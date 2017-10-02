# global options
std_basis = True # (trace subgroup, trace kernel) whenever possible, (quasi-trace subgroup, quasi-traceless subgroup) for binary order
verbose = True
tests = 50

lA, lB = 3, 5
eA, eB = 4, 3 
f = 4 # this way p = 3 (mod 4), F_{p^2} = F_p[x]/<x^2 + 1>, and E0: y^2 = x^3 + x is supersingular
p = (lA^eA*lB^eB*f) - 1
if lA == 2:
    print "subgroups: binary and odd"
else:
    print "subgroups: both odd"
if verbose:
    print "p =", p
assert p.is_prime()

Fp = GF(p)
Rp.<x> = Fp[]
Fp2.<i> = Fp.extension(x^2 + 1)
#print Fp2
#print charpoly(i, 'i')

# The reduced Tate pairing:
def Tate(P, Q, n):
    assert (p^2 - 1) % n == 0
    z = (p^2 - 1) // n
    f = P._miller_(Q, n)
    if f == 0:
        return 1
    else:
        return f^z

#The trace function:
def Trace(E, P):
    T = E(P[0]^p, P[1]^p, P[2]^p)
    half = inverse_mod(2, P.order())
    return half*(P + T)

def ChooseOffset():
    if verbose:
        print "offset w..."
    # choose coefficients:
    alpha = lA*ZZ.random_element(1, lA^(eA - 1) - 1)
    beta  = lA*ZZ.random_element(0, lA^(eA - 1) - 1) + ZZ.random_element(1, lA - 1)
    gamma = lA^eA - alpha^2*inverse_mod(beta, lA^eA) % lA^eA
    delta = lA^eA - alpha
    assert gamma % lA == 0 and alpha % lA == 0 and delta % lA == 0 and beta % lA != 0
    # ensure that no solution to (gamma*x^2 + 2*alpha*x - beta) = 0 (mod lA^eA) exists:
    assert (alpha^2 + beta*gamma) % lA^eA == 0
    for x in range(0, lA):
        assert (gamma*x^2 + 2*alpha*x - beta) % lA != 0
    assert (alpha*delta - beta*gamma) % lA^eA == 0
    for x in range(0, lA^eA):
        assert (gamma*x^2 + 2*alpha*x - beta) % lA^eA != 0
    return alpha, beta, gamma, delta

# The public supersingular curve E0
E0 = EllipticCurve(Fp2, [1, 0]) # y^2 = x^3 + x
if verbose:
    print "E0..."
#assert E0.abelian_group()
assert E0.is_supersingular()
assert E0.order() == ((lA^eA)*(lB^eB)*f)^2

while tests > 0:
    print "======== tests to go:", tests
    tests -= 1

    # public points PA, QA:
    if verbose:
        print "PA, QA..."
    if std_basis:
        loop = True
        while loop:
            PQ = lB^eB*f*E0.random_point()
            PA = Trace(E0, PQ)
            QA = PQ - Trace(E0, PQ)
            loop = (PA.order() != lA^eA) or (QA.order() != lA^eA) # just to avoid subgroups of order lB^kB, kB < eB
        gA = PA.weil_pairing(QA, lA^eA) # automatically nonzero (the trace group and the trace-zero group are pairing eigengroups)
        assert Trace(E0, PA) != E0(0)
        assert Trace(E0, PA) == PA
        assert Trace(E0, QA) == E0(0)
    else:
        loop = True
        while loop:
            PA = lB^eB*f*E0.random_point()
            loop = PA.order() != lA^eA
        loop = True
        while loop:
            QA = lB^eB*f*E0.random_point()
            gA = PA.weil_pairing(QA, lA^eA)
            loop = (QA.order() != lA^eA) or (gA == 1)
    #print "PA =", PA, "ord(PA) =", PA.order(), "tr(PA) =", Trace(E0, PA)
    #print "QA =", QA, "ord(QA) =", QA.order(), "tr(QA) =", Trace(E0, QA)
    # Check linear independence of PA and QA:
    gA = PA.weil_pairing(QA, lA^eA)
    #print "gA =", gA
    assert PA.order() == lA^eA
    assert QA.order() == lA^eA
    assert gA != 1

    # public points PB, QB:
    if verbose:
        print "PB, QB..."
    if std_basis:
        loop = True
        while loop:
            PQ = lA^eA*f*E0.random_point()
            PB = Trace(E0, PQ)
            QB = PQ - Trace(E0, PQ)
            loop = (PB.order() != lB^eB) or (QB.order() != lB^eB) # just to avoid subgroups of order lB^kB, kB < eB
        gB = PB.weil_pairing(QB, lB^eB) # automatically nonzero (the trace group and the trace-zero group are pairing eigengroups)
        assert Trace(E0, PB) != E0(0)
        assert Trace(E0, PB) == PB
        assert Trace(E0, QB) == E0(0)
    else:
        loop = True
        while loop:
            PB = lA^eA*f*E0.random_point()
            loop = PB.order() != lB^eB
        loop = True
        while loop:
            QB = lA^eA*f*E0.random_point()
            gB = PB.weil_pairing(QB, lB^eB)
            loop = (QB.order() != lB^eB) or (gB == 1)
    #print "PB =", PB, "ord(PB) =", PB.order(), "tr(PB) =", Trace(E0, PB)
    #print "QB =", QB, "ord(QB) =", QB.order(), "tr(QB) =", Trace(E0, QB)
    # Check linear independence of PA and QA:
    #print "gB =", gB
    assert PB.order() == lB^eB
    assert QB.order() == lB^eB
    assert gB != 1

    # shared offset:
    alpha, beta, gamma, delta = ChooseOffset()
    if verbose:
        print "alpha = ", alpha, " beta = ", beta, " gamma = ", gamma, " delta = ", delta

    # Alice's key pair generation
    if verbose:
        print "rA..."
    loop = True
    while loop:
        rA = ZZ.random_element(1, lA^eA - 1)
        RA = PA + rA*QA
        loop = RA.order() != lA^eA
    if verbose:
        print "rA =", rA
    if verbose:
        print "phiA, EA..."
    phiA = E0.isogeny(RA)
    EA = phiA.codomain()
    assert E0.is_isogenous(EA)
    if verbose:
        print "GA, HA..."
    GA, HA = phiA(PB), phiA(QB)
    assert GA.order() == lB^eB
    assert HA.order() == lB^eB
    gAA = GA.weil_pairing(HA, lB^eB)
    #print "gAA =", gAA
    assert gAA != 1

    # Bob's key pair generation
    if verbose:
        print "rB..."
    loop = True
    while loop:
        rB = ZZ.random_element(1, lB^eB - 1)
        RB = PB + rB*QB
        loop = RB.order() != lB^eB
    if verbose:
        print "rB =", rB
    if verbose:
        print "phiB, EB..."
    phiB = E0.isogeny(RB)
    EB = phiB.codomain()
    assert E0.is_isogenous(EB)
    if verbose:
        print "GB, HB..."
    GB, HB = phiB(PA), phiB(QA)
    assert GB.order() == lA^eA
    assert HB.order() == lA^eA
    gBB = GB.weil_pairing(HB, lA^eA)
    #print "gBB =", gBB
    assert gBB != 1
    #print "GB = ", GB
    #print "HB = ", HB

    if verbose:
        print "U, V..."
    U, V = alpha*GB + beta*HB, gamma*GB + delta*HB # NB: V = -(alpha/beta)*U
    if verbose:
        print "U =", U, "V =", V
        print "ord(U) =", U.order(), "ord(V) =", V.order()
    gUV = U.weil_pairing(V, lA^eA)
    assert gUV == 1

    hatGB = GB - U
    hatHB = HB - V
    assert hatGB.order() == lA^eA
    assert hatHB.order() == lA^eA

    mu = ZZ.random_element(1, lA^eA - 1)
    if verbose:
        print "mu =", mu
    tahGB = GB + mu*U
    tahHB = HB + mu*V
    assert tahGB.order() == lA^eA
    assert tahHB.order() == lA^eA

    if verbose:
        print "Weil check..."
    e = GB.weil_pairing(HB, lA^eA)
    c = (PA.weil_pairing(QA, lA^eA))^(lB^eB)
    d = hatGB.weil_pairing(hatHB, lA^eA)
    h = tahGB.weil_pairing(tahHB, lA^eA)
    if verbose:
        print "w(GB, HB)           = ", e
        print "w(PA, QA)^(lB^eB)   = ", c
        print "w(GB-U, HB-V)       = ", d
        print "w(GB+mu*U, HB+mu*V) = ", h
        #print "distinguish? ", d != c or h != c
    assert e == c
    assert c == d
    assert c == h
    #print "e^(lA^eA) = ", e^(lA^eA)
    #print "c^(lA^eA) = ", c^(lA^eA)
    #print "d^(lA^eA) = ", d^(lA^eA)
    #print "h^(lA^eA) = ", h^(lA^eA)

    if verbose:
        print "Tate check..."
    e = Tate(GB, HB, lA^eA)
    c = Tate(PA, QA, lA^eA)^(lB^eB)
    d = Tate(hatGB, hatHB, lA^eA)
    h = Tate(tahGB, tahHB, lA^eA)
    if verbose:
        print "t(GB, HB)           = ", e
        print "t(PA, QA)^(lB^eB)   = ", c
        print "t(GB-U, HB-V)       = ", d
        print "t(GB+mu*U, HB+mu*V) = ", h
        #print "distinguish? ", d != c or h != c
    assert e == c
    assert c == d
    assert c == h
    #print "e^(lA^eA) = ", e^(lA^eA)
    #print "c^(lA^eA) = ", c^(lA^eA)
    #print "d^(lA^eA) = ", d^(lA^eA)
    #print "h^(lA^eA) = ", h^(lA^eA)

    if verbose:
        print "kernel check..."
    kerPrime = GB + rA*HB;
    kerShift = hatGB + rA*hatHB
    gpp = kerPrime.weil_pairing(kerPrime, lA^eA)
    #print "gpp = ", gpp
    gps = kerPrime.weil_pairing(kerShift, lA^eA)
    #print "gps = ", gps
    assert gpp == 1
    assert gps != 1

    phiAPrime = EB.isogeny(kerPrime)
    EBA = phiAPrime.codomain()
    #print "phiA'(ker') = ", phiAPrime(kerPrime)
    #print "phiA'(ker$) = ", phiAPrime(kerShift)
    assert phiAPrime(kerPrime) == EBA(0)
    assert phiAPrime(kerShift) != EBA(0)

    if verbose:
        print "j-invariant check..."
    j = EBA.j_invariant()
    #print "j  = ", j
    phiAShift = EB.isogeny(kerShift)
    EBAShift = phiAShift.codomain()
    jShift = EBAShift.j_invariant()
    #print "j$ = ", jShift
    #print "j match? ", j == jShift
    assert j != jShift
    if verbose:
        print "**** ok so far!"

print "======== all tests ok!" # otherwise an assertion has not been satisfied
