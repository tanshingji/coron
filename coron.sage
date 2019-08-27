# Implementation of Coron's version of Coppersmith's algorithm for bivariate polynomials
# Returns integer roots of a bivariate polynomial bounded by X, Y
# Referenced paper: https://link.springer.com/content/pdf/10.1007%2F978-3-540-74143-5_21.pdf
# Using Theorem 2 in paper: bounds X*Y < W^(2/(3*delta)), taking separate degrees in x and y
# For exhaustive search method: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.127.7176&rep=rep1&type=pdf

# Compute the matrix S
# Used to set n:= |det(S)|
def compute_S(f, k, i_0, j_0):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])

    # Define all polynomials s_ab(x,y) = x^a * y^b * f(x,y) for 0 <= a,b < k
    s_ab = []
    for a in range(k):
        for b in range(k):
            s_ab.append(x^a * y^b * f)

    # Define matrix S: rows are coefficients of s_ab(x,y) but only in monomials x^(i_0 + i) * y^(j_0 + j)
    S = matrix(ZZ, k^2, k^2)

    for row in range(len(s_ab)):
        for i in range(k):
            for j in range(k):
                S[row, k*i + j] = s_ab[row].monomial_coefficient(x^(i_0 + i) * y^(j_0 + j))

    return S



# Choose suitable (i_0, j_0) to maximise quantity in Lemma 3 (for n := det(S) != 0)
def choose_index(f, X, Y, k):
    R.<x, y> = ZZ[]
    W = max([abs(coeff) for coeff in f(x*X, y*Y).coefficients()])
    delta = max([f.degree(x), f.degree(y)])

    # Get indices (u, v), for which W = |f_ij| * X^i * Y^j
    for (monomial, coeff) in zip(f(x*X, y*Y).monomials(), f(x*X, y*Y).coefficients()):
        if W == abs(coeff):
            u, v = monomial.degrees()
            break

    # Choose (i_0, j_0) that maximise 8^((i - u)^2 + (j - v)^2) * |f_ij| * X^i * Y^j
    maximal_value = 0
    i_0, j_0 = 0, 0

    for i in range(delta + 1):
        for j in range(delta + 1):
            value = 8^((i - u)^2 + (j - v)^2) * abs(int(f.coefficient({x:i, y:j}))) * X^i * Y^j
            if value >= maximal_value:
                maximal_value = value
                i_0, j_0 = i, j

    return i_0, j_0



# Constructs ordered list of monomials with those those we wish to later ignore on the left
# Makes cutting out L_2 from M cleaner (want to cut out bottom right as in paper)
# We don't care about the order of the monomials as long as they are on the correct respective sides
def monomial_constructor(f, k, i_0, j_0):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])

    # Ignored monomials on the left
    monomials = [x^(i_0 + i) * y^(j_0 + j) for i in range(k) for j in range(k)]
    assert(len(monomials) == k^2)

    for i in range(k + delta):
        for j in range(k + delta):
            monomial = x^i * y^j
            if monomial not in monomials:
                monomials.append(monomial)

    assert(len(monomials) == (k + delta)^2)

    return monomials



# Checks conditions for Theorem 2 and Lemma 2, and implication from Lemma 3 if debug=True in bivariate_coppersmith()
def check_inequalities(f, X, Y, k, h_norm):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])
    omega == (k + delta)^2 - k^2
    S = compute_S(f, k, i_0, j_0)
    i_0, j_0 = choose_index(f, X, Y, k)
    n = abs(det(S))

    # Check Theorem 2 (Coppersmith) bounds
    if X * Y >= W^(2/(3*delta)):
        raise ValueError("Theorem 2 (Coppermsith) bounds X * Y < W^(2/(3*delta)) not satisfied.")

    # Check Lemma 2 (Howgrave-Graham) bounds
    if h_norm >= n / sqrt(omega):
        raise ValueError("Lemma 2 (Howgrave-Graham) bounds ||h(x*X, y*Y)|| < n/sqrt(omega) not satisfied.")

    # Check implication from Lemma 3
    lower_bound = (W / (X^i_0 * Y^j_0))^(k^2) * 2^((-6*k^2) * (delta^2) - 2*k^2)
    upper_bound = (W / (X^i_0 * Y^j_0))^(k^2) * 2^(k^2)

    if not lower_bound <= n <= upper_bound:
        raise ValueError("Lemma 3 bounds not satisfied, unable to find indices (i_0, j_0).")



# Returns integer roots of polynomial f bounded by X and Y, if any
# Checks certain conditions in the paper if debug=True using check_inequalities
def bivariate_coppersmith(f, X, Y, k, debug=False):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])
    i_0, j_0 = choose_index(f, X, Y, k)
    S = compute_S(f, k, i_0, j_0)
    W = max([abs(coeff) for coeff in f(x*X, y*Y).coefficients()])
    n = abs(det(S))

    # Define all polynomials s_ab(x*X, y*Y) where s_ab(x,y) = x^a * y^b * f(x,y) for 0 <= a,b < k
    s_ab = []
    for a in range(k):
        for b in range(k):
            s_ab.append((x*X)^a * (y*Y)^b * f(x*X, y*Y))

    # Define all polynomials r_ij(x*X, y*Y) where r_ij(x,y) = x^i * y^j * n for 0 <= i,j < k + delta
    r_ij = []
    for i in range(k + delta):
        for j in range(k + delta):
            r_ij.append((x*X)^i * (y*Y)^j * n)

    # Define M, matrix with row vectors the coefficients of polynomials s_ab and r_ij
    M_cols = (k + delta)^2
    M = matrix(ZZ, k^2 + M_cols, M_cols)

    # Get monomials in order
    monomials = monomial_constructor(f, k, i_0, j_0)

    # Coefficients of s_ab
    for row in range(len(s_ab)):
        for col in range(len(monomials)):
            M[row, col] = s_ab[row].monomial_coefficient(monomials[col])

    # Coefflcients of r_ij
    for row in range(len(r_ij)):
        for col in range(len(monomials)):
            M[len(s_ab) + row, col] = r_ij[row].monomial_coefficient(monomials[col])

    # Make M upper triangular
    M = M.echelon_form()

    # Get column number to cut out lattice L_2
    # Ignoring zero rows, the upper triangular matrix we have is square so col_number is also our row number
    col_number = k^2

    # Calculate dimensions of L_2
    omega = M_cols - col_number
    assert(omega == (k + delta)^2 - k^2)

    # Define L_2 (cut out bottom right of M, excluding zero rows)
    L_2 = M[col_number:M_cols, col_number:M_cols]

    # Check det(L_2)
    power = ((delta + k - 1) * (delta + k)^2)/2 - ((k - 1) * k^2)/2
    assert(abs(det(L_2)) == n^(omega - 1) * (X*Y)^power / (X^i_0 * Y^j_0)^(k^2))

    # Apply LLL on L_2
    L_2 = L_2.LLL()

    # Start constructing h(x,y) from the rows of the reduced L_2
    # Save only relevant monomials for h(x,y)
    new_monomials = monomials[col_number:]

    # Make list of monomials in X and Y to get h(x,y) from h(x*X, y*Y)
    new_monomials_XY = []
    for monomial in new_monomials:
        new_monomials_XY.append(monomial(X, Y))

    roots = []
    for row in range(omega):

        # If debug == True, check certain conditions/inequalities in paper using check_inequalities()
        if debug:
            h_norm = L_2[row].norm()
            check_inequalities(f, X, Y, k, h_norm)

        # Define h(x,y) from L_2
        # Rows of L_2 are coefficients of h(x*X, y*Y)
        h = R(0)
        for i, (monomial, monomial_XY) in enumerate(zip(new_monomials, new_monomials_XY)):
            h += L_2[row, i] * monomial // monomial_XY

        # Find Q(x), resultant of f(x,y) and h(x,y) w.r.t. y
        Q = f.resultant(h, y).univariate_polynomial()

        # Solve univariate Q to get solutions for x
        x_roots = Q.roots(multiplicities = False)

        # Solve univariate f to get solutions for y, giving us the roots
        for x_root in x_roots:
            f_y = f(x_root, y).univariate_polynomial()
            y_roots = f_y.roots(multiplicities = False)
            for y_root in y_roots:
                solution = (x_root, y_root)
                roots.append(solution)

        # Not interested in all solutions
        if len(roots) > 0:
            break

    # Remove duplicate roots
    roots = uniq(roots)

    # Test our solution
    for root in roots:
        assert(f(root) == 0)

    return roots



# Performs exhaustive search on high order bits of x_0
# Allows us to only be required to fulfill the weaker condition X*Y < W^(2/(3*delta))
# Theoretically correct method of exhaustive search that satisfies stricter bounds
# Requires sufficient number of bits for X and Y (> 17*delta + 11) to work; if not satisfied, use exhaustive_search()
# findall: set to True to get all solutions within range; set to False to only return the first solution found
def proper_exhaustive_search(f, X, Y, k, findall=False):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])
    W = max([abs(coeff) for coeff in f(x*X, y*Y).coefficients()])
    epsilon = 1 / log(W, 2)

    # TX = min{2^i | 2^i >= X}
    # Same for TY
    TX, TY = 1, 1
    if X > 1:
        while TX < X:
            TX *= 2
    else:
        TX = X
    if Y > 1:
        while TY < Y:
            TY *= 2
    else:
        TY = Y

    # Define i, where 2^i is the number of chunks to exhaustively search
    # Try low i first to speed things up
    for i in range(1, min(TX, TY).nbits()):
        X_prime = Integer(TX / (2^i))
        Y_prime = Integer(TY / (2^i))

        # Look for solution x_0 within intervals of size T/(2^i)
        solutions = []
        for jy in range(2^i):
            CY = jy * Y_prime

            for jx in range(2^i):
                CX = jx * X_prime
                f_prime = f(CX + x, CY + y)
                W_prime = max([abs(coeff) for coeff in f_prime(x*X_prime, y*Y_prime).coefficients()])
                k_prime = floor(log(W_prime, 2))

                # If condition is satisfied, take this value of i and start finding solutions
                if X_prime * Y_prime < W_prime^(2/(3*delta) - epsilon) * 2^(-14 * delta / 3):

                    # Use bivariate_coppersmith() to find the roots (x_0_prime, y_0_prime) of f_prime
                    # Roots of f are (x_0, y_0) = (CX + x_0_prime, CY + y_0_prime)
                    solutions_prime = bivariate_coppersmith(f_prime, X_prime, Y_prime, k_prime)

                    # Save solutions
                    for solution in solutions_prime:
                            solutions.append((CX + solution[0], CY + solution[1]))

                    # Check solutions hold in f
                    for solution in solutions:
                        assert(f(solution) == 0)

        # If solutions are found, stop here and return them if findall == False
            if len(solutions) > 0 and not findall:
                return uniq(solutions)

    return uniq(solutions)



# Performs exhaustive search on high order bits of x_0
# Allows us to only be required to fulfill the weaker condition X*Y < W^(2/(3*delta))
# Does NOT require us to have enough bits for X and Y; for proper method, use proper_exhaustive_search()
# findall: set to True to get all solutions within range; set to False to only return the first solution found
def exhaustive_search(f, X, Y, k, findall=False):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])
    W = max([abs(coeff) for coeff in f(x*X, y*Y).coefficients()])

    # TX = min{2^i | 2^i >= X}
    # Same for TY
    TX, TY = 1, 1
    if X > 1:
        while TX < X:
            TX *= 2
    else:
        TX = X
    if Y > 1:
        while TY < Y:
            TY *= 2
    else:
        TY = Y

    # Define i, the number of chunks to exhaustively search
    # If bounds X, Y are too small, lower i
    i = 2^delta
    while TX%i != 0 or TY%i != 0:
        i = i/2

    # Define new bounds X_prime, Y_prime
    X_prime, Y_prime = R(TX/i), R(TY/i)
    CX, CY = R(0), R(0)

    # Look for solution x_0 within intervals of size T/(2^i)
    solutions = []
    for jy in range(i + 1):
        CY = R(jy * Y_prime)

        for jx in range(i + 1):
            CX = R(jx * X_prime)
            f_prime = f(CX + x, CY + y)
            W_prime = max([abs(coeff) for coeff in f_prime(x*X_prime, y*Y_prime).coefficients()])
            k_prime = floor(log(W_prime, 2))

            # Use bivariate_coppersmith() to find the roots (x_0_prime, y_0_prime) of f_prime
            # Roots of f are (x_0, y_0) = (CX + x_0_prime, CY + y_0_prime)
            solutions_prime = bivariate_coppersmith(f_prime, X_prime, Y_prime, k_prime)

            # Save solutions
            for solution in solutions_prime:
                solutions.append((CX + solution[0], CY + solution[1]))

            # Check solutions hold in f
            for solution in solutions:
                assert(f(solution) == 0)

            # If solutions are found, stop here and return them if findall == False
            if len(solutions) > 0 and not findall:
                return uniq(solutions)

    return uniq(solutions)


# Main function
# Chooses which method of exhaustive search to use depending on number of bits of X and Y
def bivariate_solver(f, X, Y, k, findall=False):
    R.<x, y> = ZZ[]
    delta = max([f.degree(x), f.degree(y)])

    # Strict upper bound for number of bits of X and Y
    l = 17*delta + 11

    # If X, Y big enough, use proper method of exhaustive search
    if X.nbits() > l and Y.nbits() > l:
        return proper_exhaustive_search(f, X, Y, k, findall)

    # Otherwise use modified version that allows small X and Y
    else:
        return exhaustive_search(f, X, Y, k, findall)



# Test examples
if __name__ == '__main__':
    # Test solution 1, roots (21, 21), (23, 19)
    R.<x,y> = ZZ[]
    f1 = 127*x*y - 1207*x - 1461*y + 21
    X, Y = 30, 20
    k = 2
    print(bivariate_solver(f1, X, Y, k))

    # Test solution 2, root (26, 11)
    f2 = 131*x*y - 1400*x + 20*y - 1286
    X, Y = 30, 20
    k = 2
    print(bivariate_solver(f2, X, Y, k))
