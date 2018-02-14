def base_norm_condition(K,L,SK,SL,proof = True):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``L`` : a finite extension of ``K``
        - ``SK`` : a list of primes ideals of ``K``
        - ``SL`` : a list with all prime ideals of ``L`` above the primes in ``SK``
        
    OUTPUT:
        A list with the generators of free part of the kernel of the map `L(SL,2)\xrightarrow{Norm}K(SK,2)`
        and the matrix associate to this map.
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: L.<b> = K.extension(x^2-5)
        sage: SL = sum([L.primes_above(p) for p in SK],[])
        sage: base_norm_condition(K,L,SK,SL)
            ([-1, -1/2*b + 3/2], Free module of degree 4 and rank 2 over Integer Ring
             Echelon basis matrix:
             [1 0 0 0]
             [0 2 0 0])
        
        sage: K.<a> = NumberField(x^2-6)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: L.<b> = K.extension(x^2-5)
        sage: SL = sum([L.primes_above(p) for p in SK],[])
        sage: base_norm_condition(K,L,SK,SL)
            ([-1, 1/2*b + 3/2, b - a], Free module of degree 6 and rank 3 over Integer Ring
             Echelon basis matrix:
             [1 0 0 0 0 0]
             [0 2 0 0 0 0]
             [0 0 1 0 0 0])
    """
    SunitK = K.S_unit_group(S = SK,proof = proof)
    SunitL = L.S_unit_group(S = SL,proof = proof)
    M = copy(zero_matrix(ZZ,SunitL.rank(),SunitK.rank()))
    for i,g in enumerate(SunitL.gens_values()[1:]):
        M[i] = SunitK(g.norm(K)).list()[1:]
    kernel = M.left_kernel()

    return [SunitL.exp(vector([0]+g.list())) for g in kernel.matrix()],kernel.matrix()


def extend_basis_over_ZZ(T):
    r"""

    INPUT:
        - ``T`` : a matrix with integer coefficients such that the rows are less than the columns

    OUTPUT:
        A square matrix whose first columns is the matrix ``T`` and it is invertible if it is able to be done.

    EXAMPLE::

        sage:
    """
    D, U, V = T.smith_form()
    m,n = D.dimensions()
    if prod(D.diagonal()) == 1:
        Dprime = block_matrix([[zero_matrix(ZZ,n-m,m),identity_matrix(ZZ,n-m)]])
        Tprime, Uprime, Vprime = Dprime.smith_form()
        if Uprime.is_one():
            Tprime = Dprime*V.inverse()
            return block_matrix([[T],[Tprime]])
        else:
            T
    else:
        return T


def Norm_subgroup_division_field(SK,SL,hc = None,proof = True):
    r"""
    
    INPUT:
        - ``SK`` : a list of prime ideals of a number field `K`
        - ``SL`` : a list of all prime ideals of a number field `L` such that `Ga\ell(L/K)` is isomorphic to a subgroup of `S_3`
        - ``hc`` : a defining polynomial of the intermediate cubic extension in `S_3` case.

    OUTPUT:
        - ``lambda_subgroup`` : a list of generators of the subroup of `S_L`-unit group where `\lambda` lies
        - ``mu_subgroup`` : a list of generators of the subroup of `S_L`-unit group where `\mu` lies
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: SK = sum([K.primes_above(p) for p in [2,5,7]],[])
        sage: L.<a> = NumberField(x^6 + 84*x^4 + 994*x^3 + 21609*x^2 + 2058*x + 266854)
        sage: SL = sum([L.primes_above(p) for p in [2,5,7]],[])
        sage: Norm_subgroup_division_field(SK,SL)
            ([29/1190700*a^5 - 7/24300*a^4 + 323/170100*a^3 + 541/170100*a^2 + 242/1215*a - 69973/12150,
            4/297675*a^5 + 1/17010*a^4 + 47/85050*a^3 + 659/42525*a^2 + 1862/6075*a + 2057/6075,
            -11/2381400*a^5 - 1/68040*a^4 - 89/340200*a^3 + 629/340200*a^2 - 821/6075*a - 10739/24300,
            -263/1488375*a^5 + 43/30375*a^4 - 493/42525*a^3 - 15751/212625*a^2 - 66976/30375*a + 990833/30375],
            [-1/198450*a^5 + 1/5670*a^4 - 79/28350*a^3 + 859/28350*a^2 - 154/2025*a + 536/2025,
            19/850500*a^5 - 17/850500*a^4 - 11/121500*a^3 + 6647/121500*a^2 - 1783/30375*a + 8867/12150,
            -59/496125*a^5 + 1/23625*a^4 + 11/2835*a^3 - 23323/70875*a^2 + 268/1125*a - 41561/10125,
            -1/79380*a^5 - 1/18900*a^4 - 61/56700*a^3 - 661/56700*a^2 - 389/1350*a - 4633/4050])
    """
    K = SK[0].ring()
    L = SL[0].ring()
    relative_degree = L.absolute_degree()/K.absolute_degree()
    SunitL = L.S_unit_group(proof,SL)

    if relative_degree == 2:

        lambda_group = base_norm_condition(K,L,SK,SL,proof)[0]

        #we compute a basis such that some generators are units
        A = matrix(ZZ,[SunitL(g).list() for g in lambda_group])
        number_of_units_gens = len([1 for g in SunitL.gens_values() if g.is_integral() and g.absolute_norm().abs() == 1])
        U = A.matrix_from_columns(range(number_of_units_gens,A.dimensions()[1])).smith_form()[1]
        A = U*A

        return [SunitL.torsion_generator().value()]+[SunitL.exp(vector(g.list())) for g in A],SunitL.gens_values()
    elif relative_degree == 3:
        lambda_group = base_norm_condition(K,L,SK,SL,proof)[0]

        #we compute a basis such that some generators are units
        A = matrix(ZZ,[SunitL(g).list() for g in lambda_group])
        number_of_units_gens = len([1 for g in SunitL.gens_values() if g.is_integral() and g.absolute_norm().abs() == 1])
        U = A.matrix_from_columns(range(number_of_units_gens,A.dimensions()[1])).smith_form()[1]
        A = U*A
        lambda_group = [SunitL.torsion_generator().value()]+[SunitL.exp(vector(g.list())) for g in A]

        #we compute Gm
        sigma = find_sigma(L)
        mu_group = [sigma(g**(-1)) for g in lambda_group]
        
        return lambda_group,mu_group
    elif relative_degree == 6:
        if hc == None:
            raise ValueError ('You forgot the cubic polynomial')

        #the intermediate cubic
        Lc = K.extension(hc,'c')
        SLc = sum([Lc.primes_above(p) for p in SK],[])

        #M is the unique quadratic extension of K which is a subfield of L
        M = L.base_field()
        SM = sum([M.primes_above(p) for p in SK],[])

        #I define L as an extension of Lc
        Lbar = Lc.extension(M.defining_polynomial(),'bar')
        SLbar = sum([Lbar.primes_above(p) for p in SLc],[])

        #I find the identical map from L to Lbar
        for emb in Lbar.embeddings(L):
            if len([1 for gb in L.gens() if len([1 for w in emb.im_gens() if w == gb]) > 0]) == len(emb.im_gens()):
                embLbartoL = emb

        #I find the two kenrel
        AM = base_norm_condition(M,L,SM,SL,proof)

        ALc = base_norm_condition(Lc,Lbar,SLc,SLbar,proof)

        #I compute the intersection of the two kernels

        mat = zero_matrix(ZZ,len(ALc[0]),SunitL.rank())
        for i,g in enumerate(ALc[0]):
            mat[i] = SunitL(embLbartoL(g)).list()[1:]

        A = block_matrix(ZZ,[[AM[1]],[-mat]])
        B = A.left_kernel().matrix()
        lambda_group = [SunitL.exp(vector([0]+(r[:len(AM[0])] * AM[1]).list())) for r in B.rows()]

        #we compute a basis such that some generators are units
        A = matrix(ZZ,[SunitL(g).list() for g in lambda_group])
        number_of_units_gens = len([1 for g in SunitL.gens_values() if g.is_integral() and g.absolute_norm().abs() == 1])
        U = A.matrix_from_columns(range(number_of_units_gens,A.dimensions()[1])).smith_form()[1]
        A = U*A

        lambda_group = [SunitL.torsion_generator().value()]+[SunitL.exp(vector(g.list())) for g in A]
        sigma = find_sigma(L)
        return lambda_group, [sigma(g**(-1)) for g in lambda_group]