def tame_hilbert_symbol_over_QQ(a,b,p,n):
    r"""
    
    INPUT:
        - ``a`` : an integer
        - ``b`` : an integer
        - ``p`` : a prime ideal
        - ``n`` : a natural number
        
    OUTPUT:
        The exponent of the general Hilbert symbol `\left(\frac{,}{p}\right):\mathbb Q_p/\mathbb Q_p^{*n}\times\mathbb Q_p/\mathbb Q_p^{*n}\rightarrow\mu_n` when `n\mid p-1` or `n=2` for `p=2`.
    
    EXAMPLE::
        
        sage: tame_hilbert_symbol_over_QQ(3,7,7,6)
            5
        
        sage: tame_hilbert_symbol_over_QQ(3,7,5,2)
            0
    """
    if a == 0 or b == 0:
        raise ValueError('Either a or b is equal to 0')
    if p == 2 and n != 2:
        raise ValueError('p=2 but n is different from 2')
    if p == 2 and n == 2:
        if hilbert_symbol(a,b,p) == -1:
            return 1
        else:
            return 0
    if (p-1) % n !=0 :
        raise ValueError('n does not divide p-1')
        
    l = a.valuation(p)
    m = b.valuation(p)
    t = (p-1)/n
    w = (-1)**(l*m) * b**l/a**m
    GF = FiniteField(p)
    
    return (GF(w)**t).log()


def tame_hilbert_symbol(a,b,prime,n):
    r"""
    
    INPUT:
        - ``a`` : a nonzero element of number field `K`
        - ``b`` : a nonzero element of number field `K`
        - ``prime`` : a prime ideal
        - ``n`` : a natural number
        
    OUTPUT:
        The exponent of the general Hilbert symbol `\left(\frac{,}{p}\right):K_{\mathcal p}/K_{\mathcal p}^{*n}\times K_{\mathcal p}/K_{\mathcal p}^{*n}\rightarrow\mu_n` when `n\mid q-1` or `n=2` for `p=2`, where `q` is the order of the residue field of `\mathcal p`.
    
    EXAMPLE::
        
        sage: K.<i> = QuadraticField(-1)
        sage: p1 = K.prime_above(3)
        sage: tame_hilbert_symbol(3,3,p1,8)
            4
            
        sage: tame_hilbert_symbol(3,7,7,6)
            5
    """
    if prime in QQ:
        return tame_hilbert_symbol_over_QQ(a,b,prime,n)
    K = prime.number_field()
    p = prime.absolute_norm().factor()[0][0]
    GF = prime.residue_field()
    q = GF.cardinality()
    if a.is_zero() or b.is_zero():
        raise ValueError('Either a or b is equal to 0')
    if n == 2:
        if pari(K).nfhilbert(a, b, prime.pari_prime()) == -1:
            return 1
        else:
            return 0
    if (q-1) % n != 0:
        raise ValueError('n does not divide p-1')
        
    l = K(a).valuation(prime)
    m = K(b).valuation(prime)
    t = (q-1)/n
    w = (-1)**(l*m) * b**l/a**m

    return (GF(w)**t).log(GF.primitive_element())


def is_S_principal(I,S):
    r"""

    INPUT:
        - ``I`` : a fractional ideal of a number field `K`
        - ``S`` : a finite set of primes of `K`

    OUTPUT:
        - True, if the natural image of ``I`` in the group of S-ideals is principal, otherwise False
        - a generator if ``I`` is a principal S-ideal, otherwise ``I``

    EXAMPLE::

        sage:
    """
    if S == []:
        if I.is_principal():
            return True,I.gens_reduced()[0]
        else:
            return False,I

    K = I.ring()
    Cl = K.class_group()


    if Cl(I).is_trivial():
        return True, I.gens_reduced()[0]

    C = diagonal_matrix(Cl.gens_orders())
    A = matrix(ZZ,[Cl(p).list() for p in S])
    AC = block_matrix([[A],[C]])
    B = matrix(ZZ,Cl(I).list())
    ACB = block_matrix([[AC],[B]])
    print 'AC',AC
    print 'ACB',ACB

    #we check if the matrices AC and ACB define the same Z-module

    if AC.row_module().index_in(ACB.row_module()) == 1:
        v = AC.solve_left(-B)[0]
        J = I*prod([p**e for p,e in zip(S,v)])
        return True,J.gens_reduced()[0]
    else:
        return False,I


def in_CKSn(I,S,n):
    r"""

    INPUT:
        - ``I`` : a fractional ideal of a number field `K`
        - ``S`` : a finite set of prime ideals of `K`
        - ``n``: a natural number

    OUTPUT:
        True, if the natural image of ``I`` in `\mathcal C_{K,S}` lies in `\mathcal C_{K,S}[n]`.

    EXAMPLE::

        sage:
    """

    fac = (I**n).factor()
    J = I.parent().ring().ideal(1)
    for prime in fac:
        if prime[0] in S:
            J *= prime[0]**prime[1]

    return (I**n/J).is_principal()


def in_nCKSmn(I,S,m,n):
    r"""

    INPUT:
        - ``I`` : a fractional ideal of a number field `K`
        - ``S`` : a finite set of prime ideals of `K`
        - ``m``: a natural number
        - ``n`` : a natural number

    OUTPUT:
        - True, if the natural image of ``I`` in `\mathcal C_{K,S}` lies in `n\mathcal C_{K,S}[mn]`.
        - If True, an ideal `J` such that `I=J^n` in the `S`-class group. Otherwise, I
    EXAMPLE::

        sage:
    """

    K = I.ring()
    Cls = K.S_class_group(S)
    gens = Cls.gens_ideals()
    orders = Cls(I).list()
    J = K.ideal(1)
    for i,t in enumerate(orders):
        if t%(m*n) != 0:
            return False,I
        else:
            print 't/m',t/m
            J *= gens[i]**(t/m)

    return True,J


def in_KSn(x,S,n):
    r"""

    INPUT:
        - ``x`` : an element in a number field `K`
        - ``S`` : a set of finite ideals of `K`
        - ``n`` : a natural number

    OUTPUT:
        True, if `x\in K(S,n)`, otherwise False

    """

    for prime in x.parent().ideal(x).factor():
        if prime[0] not in S and prime[1]%n != 0:
            return False

    return True


def brace_map(a,S,n):
    r"""
    
    INPUT:
        - ``a`` : an element of the `K(S,p)` Selmer group of a number field `K`
        - ``S`` : a set of prime ideals of `K`
        - ``n`` : a natural number
    
    OUTPUT:
        - ``b`` : a vector that represents [a] in S - Class group of `K`
        - ``J`` : the fractional ideal that represents [a] in S - Class group of `K`
    
    COMMENT:
        
        It is the image of the surjective map on the short exact sequence 
        
        `1\longrightarrow\mathcal O^*_{K,S}/\mathcal O^{*n}_{K,S}\xrightarrow{i} K(S,n)\xrightarrow{[a]}\mathcal C_{K,S}[n]\longrightarrow 1`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-41)
        sage: S = K.primes_above(41)
        sage: Cls = K.S_class_group(S)
        sage: Cls
            S-class group of order 8 with structure C8 of Number Field in a with defining polynomial x^2 + 41
        sage: K.ideal(2).factor()
            (Fractional ideal (2, a + 1))^2
        sage: brace_map(K(2),S,2)
            ([4], Fractional ideal (2, a + 1))
        sage: K.ideal(3).factor()
            (Fractional ideal (3, a + 1)) * (Fractional ideal (3, a + 2))
        sage: brace_map(K(3),S,2)
            ValueError: The element a does not lie in K(S,p)     
    """
    
    K = a.parent()
    Cls = K.S_class_group(S=S)
    fac = K.ideal(a).factor()
    J = K.ideal(1)
    for prime in fac:
        if prime[0] not in S:
            if prime[1] % n != 0:
                raise ValueError('The element a does not lie in K(S,n)')
            m = prime[1]/n
            J = J*(prime[0])**m

    b = Cls(J).list()
    
    return b,J


def generator_S_principle_ideal(J,S):
    r"""
    
    INPUT:
        - ``J`` : a fractional ideal which is a principal S - ideal
        - ``S`` : a list of prime ideals of a number field `K`
    
    OUTPUT:
        A generator for the principal S - ideal J
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-41)
        sage: S = K.primes_above(2)
        sage: I = S[0]
        sage: Cls = K.S_class_group(S)
        sage: Cl = K.class_group()
        sage: Cl(I).order()
            2
        sage: generator_S_principle_ideal(I,S)
            1
        sage: J = K.class_group().gen().ideal()
        sage: Cl(J).order()
            8
        sage: generator_S_principle_ideal(J,S)
            ValueError: J is not a principal S - ideal
    """
    K = J.number_field()
    Cl = K.class_group()
    Cls = K.S_class_group(S)
    
    #We find a product I of ideals of S such that J*I is principal 
    
    gens_ord = Cl.gens_orders()
    card_S = len(S)
    card_gens_ord = len(gens_ord)
    M = matrix(ZZ,card_S+card_gens_ord,card_gens_ord)
    D = diagonal_matrix(ZZ,card_gens_ord,vector(gens_ord));
    for i,I in enumerate(S):
        M[i] = vector(Cl(I).list())
    for i,d in enumerate(D):
        M[i+card_S] = d
           
    A = -vector(Cl(J).list())
    X = M.solve_left(A)
    I = K.ideal(1)
    for i,N in enumerate(S):
        if X[i] not in ZZ:
            raise ValueError('J is not a principal S - ideal')
        I = I*N**(X[i])
    
    J = I*J
    return J.gens_reduced()[0]


def reorder(A,n):
    r"""
    
    INPUT:
        - ``A`` : a list
        - ``n`` : a natural positive number
        
    OUTPUT:
        A list with the same length ``m`` as ``A`` and its first ``n``-th elements are the last ``n``-th elements of ``A`` and its last ``(m-n)``-th elements are the first ``(m-n)`` elements of ``A``.
        
    EXAMPLE::
        
        sage: A = [1,2,3,4,5]
        sage: reorder(A,3)
            [3, 4, 5, 1, 2]
        
        sage: B = [5,6,6,7,9]
        sage: reorder(B,5)
            [5, 6, 6, 7, 9]
        
        sage: C = [5,10,6,7]
        sage: reorder(C,5)
            ValueError: n is bigger than the length of A
        
    """
    m = len(A)
    if n>m:
        raise ValueError('n is bigger than the length of A')
    S = [a for a in A[0:m-n]]
    T = [a for a in A[m-n:m]]
    
    return T+S


def list_selmer_group(a,S,p):
    r"""
    
    INPUT:
        - ``a`` : an element in the Selmer group `K(S,p)` of a number field `K`
        - ``S`` : a list of prime ideals of K
        - ``p`` : a natural prime number
    
    OUTPUT:
        Return a copy of the exponent vector with respect of the generators that K.selmer_group(S,p) function gives
    
    COMMENT:
        The algorithm is based on the short exact sequence
        
        `1\longrightarrow\mathcal O^*_{K,S}/\mathcal O^{*p}_{K,S}\xrightarrow{i} K(S,p)\xrightarrow{[a]}\mathcal C_{K,S}[p]\longrightarrow 1`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: Sel = K.selmer_group(S,3)
        sage: w = Sel[0]^2*Sel[2]*Sel[1]^5
        sage: list_selmer_group(w,S,3)
            (2, 2, 1, 0)
            
        sage: K.<a> = NumberField(x^2-6)
        sage: S = sum([K.primes_above(p) for p in []],[])
        sage: Sel = K.selmer_group(S,2)
        sage: w = Sel[0]
        sage: list_selmer_group(w,S,2)
            (1, 0)       
    """
    if p not in Primes():
        raise ValueError('p is not a prime')
    
    K = a.parent()
    Cls = K.S_class_group(S=S)
    Sunit = K.S_unit_group(S=S)
    Sel = K.selmer_group(S,p)   
    
    M = matrix(ZZ,len(Sel),len(Cls.gens()))
    j = 0
    for u in Sel:
        r = vector(brace_map(u,S,p)[0])
        M.set_row(j,r)
        j += 1
       
    b = vector(brace_map(K(a),S,p)[0])
    A = M.solve_left(b)   
    
    y = 1
    for s,t in zip(Sel,A):
         y=y*s**t
         
    u = a/y
    v = brace_map(u,S,p)[1]
    gen = generator_S_principle_ideal(v,S)
    t = u*gen**(-p)
    
    Sunit_part = vector(ZZ,len(Sel))
    t_list = Sunit(t).list()
    j = 0
    for i,gen in enumerate(Sunit.gens()):
        if gen.order() == Infinity or gen.order().gcd(p) != 1:
            Sunit_part[j] = t_list[i]
            j += 1
            
    n = len([g for g in Sel if g.absolute_norm() == 1 or g.absolute_norm() == -1])
    Sunit_part = vector(reorder(list(Sunit_part),len(Sel)-n))
    v = Sunit_part + A
    v = v.change_ring(Integers(p))
    
    return v


def exp_p(a,prime,M):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``M`` : A positive integer
    
    OUTPUT:
        The `\mathfrak p-adic` exponential of ``a`` with respect to ``prime`` with accuary `p^M`, where `p` is the rational prime below ``prime``
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-2)
        sage: prime = K.ideal(a^3+1)
        sage: exp_p(a^3+1,prime,40)
            18258004137372707959101180869188831621509143332534131847/629590636134106\
            2871682271657666195529704407040000000000*a^3 +
            611037342146131657112686716139399492861248185433069281/21989378835566212\
            2356549929219959035044823040000000000*a^2 +
            2486870195746358623396592994809122223940417047969210857/1359343418925911\
            301840490471541564943913451520000000000*a +
            43407236459390842010586204501508547322377865800075980307/119622220865480\
            19456196316149565771506438373376000000000   
    """
    if M < 0:
        raise ValueError('M is negative')

    g = prime.ring().gen()
    e = prime.absolute_ramification_index()
    p = prime.absolute_norm().factor()[0][0]
    if a.valuation(prime) <= e/(p-1):
        raise ValueError('The element a does not have the right valuation at prime')
    
    N = 1
    while N < e*(Integer(N).factorial().valuation(p)+M)/a.valuation(prime):
        N += 1
        
    factorial = 1
    exp = 1
    z = a
    for i in range(2,N+1):
        exp += z/factorial
        factorial *= i
        z *= a
    exp_p = 0
    for i,b in enumerate(exp.list()):
        val = b.valuation(p)
        if val < 0:
            t = b * p**(-val)
            t = ZZ(mod(t,p**(M-val)))
            t = t * p**val
        else:
            t = ZZ(mod(b,p**M))
        exp_p = exp_p + t * g**i


    return exp_p


def log_p(a,prime,M):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of the number field `K`
        - ``M`` : a positive integer
    
    OUPUT:
        The `\mathfrak p-adic` logarithm of a with respect to ``prime`` and accuracy `p^M`, where `p` is the rational prime below ``prime``
        
    COMMENT:
        Here we take into account the other primes in `K` above `p` in order to take coefficients with small values
        
    Example::
        
        sage: K.<a> = NumberField(x^2+14)
        sage: p1 = K.primes_above(3)[0]
        sage: p1
            Fractional ideal (3, a + 1)
        sage: log_p(a+2,p1,20)
            1068278195*a + 734401439
            
        sage: K.<a> = NumberField(x^4+14)
        sage: p1 = K.primes_above(5)[0]
        sage: p1
            Fractional ideal (5, a + 1)
        sage: log_p(1/(a^2-4),p1,30)
            -6082090776100252917421/5*a^3 - 5206581049546514677341/5*a^2 -
            12020643872593790461691/25*a - 17711088212203601903706/25
        
            
    """
    if a == 0:
        raise ValueError('a is the zero element')
    
    if a.valuation(prime) != 0:
        raise ValueError('The valuation of a with respect to prime is not zero')

    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    
    #In order to get an approximation with small coefficients we have to take into account the other primes above p with negative valuation
    
    primes = [(-(a.valuation(pr)),pr) for pr in K.primes_above(p) if a.valuation(pr) < 0]
    list = []

    for (val,pr) in primes: 
        #for its pair in primes we find an element in K such that it is divisible only by pr and not by any other ideal above p. Then we take this element in the correct exponent
        # print 'log_p'

        # if pr.is_principal():
        #     list.append(pr.gens_reduced()[0]**val)
        # else:
        list.append(pr.gens()[1]**val)
        # print 'log_p'


    return log_p_series_part(a * prod(list),prime,M) - sum([log_p_series_part(b,prime,M) for b in list])


def log_p_series_part(a,prime,precision):
    r"""

    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of the number field `K`
        - ``precision`` : the precision of the computation

    OUPUT:
        The `\mathfrak p-adic` logarithm of a with respect to ``prime`` and accuracy `p^M`, where `p` is the rational prime below ``prime``

    COMMENT:
        The algorithm is based on the algorithm page 30 of the reference

    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.

    EXAMPLE::

        sage: K.<a> = NumberField(x^2-5)
        sage: p1 = K.primes_above(3)[0]
        sage: p1
            Fractional ideal (3)
        sage: log_p_series_part(a^2-a+1,p1,30)
            120042736778562*a + 57497887435443

        sage: K.<a> = NumberField(x^4+14)
        sage: p1 = K.primes_above(5)[0]
        sage: p1
            Fractional ideal (5, a + 1)
        sage: log_p_series_part(1/(a^2-4),p1,30)
            143842771317132543834315137804216958834805571417161458644303555788803708\
            397256757062310978903907667409633861253921/18367099231598242312011508394\
            0975887159166493245638675235742454106002696789801120758056640625*a^2 +
            980470833745295017108554730448537715484438011434976509072834104950631953\
            52344619740974087640280522130685500861874/183670992315982423120115083940\
            975887159166493245638675235742454106002696789801120758056640625
    """

    if a.valuation(prime) != 0:
        raise ValueError('The valuation of a with respect to prime is not zero')

    K = prime.ring()
    g = K.gen()
    p = prime.smallest_integer()
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    q = p**f - 1

    divisor = q.divisors()
    order = min([d for d in divisor if (a**d - 1).valuation(prime) > 0])
    gamma= a**order
    t = 0

    while (gamma-1).valuation(prime) <= e:
        t += 1
        gamma = gamma**p

    M = t + precision
    m = (gamma - 1).valuation(prime)/e

    n = Integer(1)
    step = 10 **(RR(log(M)/log(10))).floor()

    while n < (log(n)/log(p) + M)/m:
        n += step

    w = RR((log(M)/log(p))).floor()

    gamma = sum([ZZ(gi%(p**(M+w)))* g**i if gi.valuation(p) >= 0 else ZZ((gi * p**(-gi.valuation(p)))%(p**(M+w-gi.valuation(p)))) * p**(gi.valuation(p)) * g**i for i,gi in enumerate(gamma) if gi != 0],0)

    beta = 0
    delta = 1-gamma
    for i in range(1,n+1):
        beta -= delta/i
        delta *= (1-gamma)
        delta = sum([ZZ(di%(p**(M+w)))* g**e if di.valuation(p) >= 0 else ZZ((di * p**(-di.valuation(p)))%(p**(M+w-di.valuation(p)))) * p**(di.valuation(p)) * g**e for e,di in enumerate(delta) if di != 0],0)

    beta = beta/(order*p**t)

    #we try to make the coefficients small

    logp = 0
    for i,b in enumerate(beta):
        val = b.valuation(p)
        if val < 0:
            t = b * p**(-val)
            t = ZZ(mod(t,p**(M -val)))
            t = t * p**val
        else:
            t = ZZ(mod(b,p**M))
        logp = logp + t * g**i

    return logp
    
    
def defining_polynomial_for_Kp(prime,M):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``M`` : a positive natural number
        
    OUTPUT:
        A polynomial with integer coefficients that is equivelant `\mod p^M` to the defining polynomial of the completion of `K` associate to the definig polynomial of `K`
    
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(2)
        sage: p2 = K.prime_above(7); p2
            Fractional ideal (-2*a + 1)
        sage: defining_polynomial_for_Kp(p2,10)
            x + 266983762
        
        sage: K.<a> = QuadraticField(-6)
        sage: p2 = K.prime_above(2); p2
        sage: defining_polynomial_for_Kp(p2,100)
            x^2 + 6
        sage: p5 = K.prime_above(5); p5
            Fractional ideal (5, a + 2)
        sage: defining_polynomial_for_Kp(p5,100)
            x + 3408332191958133385114942613351834100964285496304040728906961917542037
    """     
    K = prime.ring()
    if not K.is_absolute():
        raise ValueError('The number field is not an absolute extension')
    
    theta = K.gen()
    f = K.defining_polynomial()
    p = prime.absolute_norm().factor()[0][0]
    e = prime.absolute_ramification_index()
    
    find = False
    N = M
    while find == False:
        RQp = Qp(p,prec = N,type = 'capped-rel', print_mode = 'series')
        
        #We factorize f in Integers(p**M) using the factorization in Qp
                
        g = f.change_ring(RQp)
        factors = g.factor();
        
        #We are going to find which component of f is related to the prime ideal 'prime'
        
        L = [factors[i][0].change_ring(ZZ) for i in range(len(factors))]
        A = [g for g in L if (g(theta)).valuation(prime) >= e*N/2];
        
        if len(A) == 1:
            return A[0].change_ring(Integers(p**M)).change_ring(ZZ)
        else:
            N += 1  


def embedding_to_Kp(a,prime,M):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``M`` : a positive natural number
        
    OUTPUT:
        An element of K that is equivelant to ``a`` `\mod p^M` and the generator of `K` appears with exponent less than `e\cdot f`, where `p` is the rational prime below ``prime`` and `e,f` are the ramification index and residue degree, respectively.
    
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(17)
        sage: p = K.prime_above(13); p
            Fractional ideal (a - 2)
        sage: embedding_to_Kp(a-3,p,15)
            -34280483416323924357152170488129450629016974897358099396
                    
        sage: K.<a> = NumberField(x^4-2)
        sage: p = K.prime_above(7); p
            Fractional ideal (-a^2 + a - 1)
        sage: embedding_to_Kp(a^3-3,p,15)
            -1261985118949117459462968282807202378
    """
    K = prime.ring()    
    if not K.is_absolute():
        raise ValueError('K has to be an absolute extension')
    
    g = defining_polynomial_for_Kp(prime,M)
    p = prime.absolute_norm().factor()[0][0]
    gen = K.gen()
    n = g.degree()
    g = g.change_ring(QQ)
    f = K(a).lift()
    
    return K(sum([b*gen**j for j,b in enumerate(f.mod(g))]))


def is_in_G(x,G):
    r"""
    
    INPUT:
        - ``x`` : a non zero element of a number field
        - ``G`` : a list of generators of a finitely generated multiplicative subgroup of `K^*`
        
    OUTPUT:
        ``True`` if x lies in G, otherwise ``False``
    
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(15)
        sage: G = [a+1,a+2]
        sage: is_in_G((a+1)^5*(a+2),G)
            True
        sage: is_in_G(a+3,G)
            False
    """ 
    if x == 0:
        raise ValueError('x is the zero element')
    if len(G) == 0:
        raise ValueError('G is empty')
    
    K = G[0].parent()
    supp = support_of_G(G,30)[0]
    # for g in G:
    #     supp.extend([p for p in g.support() if p not in supp])
    
    SunitK = K.S_unit_group(S = supp) #G is a subgroup of SunitK
    m0 = min([g.multiplicative_order() for g in SunitK.gens()])
    m = len(SunitK.group_generators())
    k = len(G)

    #A has as rows the list of its generator of G as element of SunitK taking into account the generator
    # if the torsion part
    A = copy(zero_matrix(ZZ,k+1,m))
    
    for i,g in enumerate(G):
        A[i] = SunitK(g).list()
    A[k] = zero_vector(ZZ,m)
    A[k,0] = m0
    
    #x is in G if is in SunitK and lies in the row space of A
    
    if K.ideal(x).is_S_unit(S = supp):
        y = vector(SunitK(x).list())
        M = A.row_space()
        if y in M:
            return True
        else:
            return False
    else: 
        return False


def list_in_G(x,G):
    r"""

    INPUT:
        ``x`` : an element of a number field `K`
        ``G`` : a list of generators of a multiplicative subgroup of `K^*`

    OUTPUT:
         A vector with the exponents of ``x`` with respect to ``G``

    EXAMPLE::

        sage:
    """

    if x == 0:
        raise ValueError('x is the zero element')
    if len(G) == 0:
        raise ValueError('G is empty')

    K = G[0].parent()
    x = K(x)
    supp = support_of_G(G,30)[0]

    SunitK = K.S_unit_group(S = supp) #G is a subgroup of SunitK
    m0 = min([g.multiplicative_order() for g in SunitK.gens()])
    m = SunitK.rank()+1#len(SunitK.group_generators())
    k = len(G)

    #A has as rows the list of its generator of G as element of SunitK taking into account the generator
    # if the torsion part
    A = copy(zero_matrix(ZZ,k+1,m))
    for i,g in enumerate(G):
        A[i] = SunitK(g).list()
    A[k] = zero_vector(ZZ,m)
    A[k,0] = m0

    #x is in G if is in SunitK and lies in the row space of A

    if K.ideal(x).is_S_unit(S = supp):
        y = vector(SunitK(x).list())
        M = A.row_space()
        if y in M:
            D,U,V = A.smith_form()
            ybar = y * V
            xbar = ybar[:k] * D[:k,:k].inverse()
            return (vector(list(xbar)+[0]) * U)[:k]
        else:
            raise ValueError('x is not in G')
    else:
        raise ValueError('x is not in G')


def support_of_G(G,infinite_prec):
    r"""
    
    INPUT:
        - ``G`` : a list of generators of a multiplicative subgroup of a number field `K^*`
        - ``infinite_prec`` : the preicision of the infinite places
        
    OUTPUT:
        The finite, the real infinite and complex infinite part of the support of ``G`` respectively
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[]); 
        sage: support_of_G(K.S_unit_group(S = SK).gens_values(),100)
            ([Fractional ideal (a), Fractional ideal (a + 1), Fractional ideal (-a^2
            - 1), Fractional ideal (a^2 - 2*a - 1)], 
            [Ring morphism:
              From: Number Field in a with defining polynomial x^3 - 2
              To:   Real Field with 100 bits of precision
              Defn: a |--> 1.2599210498948731647672106073], 
            [Ring morphism:
              From: Number Field in a with defining polynomial x^3 - 2
              To:   Complex Field with 100 bits of precision
              Defn: a |--> -0.62996052494743658238360530364 + 1.0911236359717214035600726142*I])
    """
    if len(G) == 0:
        raise ValueError('G is empty')
    
    K = G[0].parent()
    Krealplaces = K.real_embeddings(prec = infinite_prec)
    Kcomplexplaces = [s for s in K.places(prec = infinite_prec) if not is_real_place(s)]

    #We find the infinite_primes
    complexsup = [c for c in Kcomplexplaces if len([a for a in G if (c(a).abs()-1).abs() >= 2**(-infinite_prec/2)])>0]
    realsup = [c for c in Krealplaces if len([a for a in G if (c(a).abs()-1).abs() >= 2**(-infinite_prec/2)])>0]

    #we find the finite primes
    finitesup = []
    for g in G:
        for p in g.support():
            if p not in finitesup:
                finitesup.append(p)

    #we reorder the finite primes such that the primes which lie above the smallest rational primes are first

    rational_primes_below = [p.absolute_norm().factor()[0][0] for p in finitesup]
    for i in range(len(finitesup)):
        for j in range(i,len(finitesup)):
            if rational_primes_below[j-1] > rational_primes_below[j]:
                temp = rational_primes_below[j-1]
                rational_primes_below[j-1] = rational_primes_below[j]
                rational_primes_below[j] = temp
                # print rational_primes_below
                temp = finitesup[j-1]
                finitesup[j-1] = finitesup[j]
                finitesup[j] = temp
    return finitesup,realsup,complexsup


def is_S_unit_element(self,u):
    r"""

    INPUT:
        - ``self`` : a S-unit group of a number field `K`
        - ``u`` : an element of the number field `K`

    OUTPUT:
        Returns `True` if ``u`` is an S-unit, `False` otherwise.

    EXAMPLE::

        sage: M.<a> = QuadraticField(2)
        sage: SM = M.primes_above(2)
        sage: is_S_unit_element(M.S_unit_group(S=SM),2)
            True
        sage: is_S_unit_element(M.S_unit_group(S=SM),3)
            False
    """
    K = self._UnitGroup__number_field
    pK = self._UnitGroup__pari_number_field
    try:
        u = K(u)
    except TypeError:
        raise ValueError("%s is not an element of %s"%(u,K))

    if self._UnitGroup__S:
        m = pK.bnfissunit(self._UnitGroup__S_unit_data, pari(u)).mattranspose()
        if m.ncols() == 0:
            return False
        else:
            return True
    else:
        if not u.is_integral() or u.norm().abs() != 1:
            return False
        else:
            return True
