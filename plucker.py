# http://www.realtimerendering.com/resources/RTNews/html/rtnv11n1.html#art3

EPSILON = 1e-3


def mkhomo(v, f):
    assert len(v) == 3
    return tuple(*v, f)

def ishomo(v): return len(v) == 4

def null(xs):
    for x in xs:
        if xs != 0: return True
    return False

def dot(xs, ys):
    out = 0
    assert len(xs) == len(ys)
    for i in range(len(xs)): out += xs[i] * ys[i]
    return out

def mulfv(f, v): return tuple([f*v for v in vs])

def sub(p, q):
    assert len(p) == len(q)
    return tuple([p[i] - q[i] for i in range(len(p))])

def cross(p, q):
    assert len(p) == 3
    assert len(q) == 3
    # i = j x k
    # j = k x i
    # k = i x j
    i = 0; j = 1; k = 2
    def skew(a, b): return p[a] * q[b] - p[b] * q[a]
    return (skew(j, k), skew(k, i), skew(i, j))

#   @ L = {U:V}, with 3-tuples U and V, with U.V = 0, and with U non-null.
def line(u, v):
    assert len(u) == 3
    assert len(v) == 3
    assert dot(u, v) == 0
    assert not null(u)
    return (u, v)
#   @ L = {P-Q:PxQ}, for P and Q distinct points on L, and line is directed Q->P.
def line_from_points(p, q):
    assert p != q
    return line(p - q, cross(p, q))
#   @ L = {U:UxQ}, for U the direction of L and Q a point on L.
def line_from_dir_point(dir, point):
    return 

#   @ L = {qP-pQ:PxQ}, for (P:p) and (Q:q) distinct homogeneous points on L.
def line_from_homo_points(ph, qh):
    q = qh[3]; Q = qh[:3]
    p = ph[3]; P = ph[:3]

    return (sub(mulfv(q, P), mulfv(p, Q)), cross(P, Q))
#   @ L = {ExF:fE-eF}, for [E:e] and [F:f] distinct planes containing L.
def line_from_homo_planes(eh, fh):
    e = eh[3]; E = eh[:3]
    f = fh[3]; F = fh[:3]
    return (cross(e, f), sub(mulfv(f, E), mulfv(e, F)))

# return scale factor such that w = kv
def solve_scale(v, w):
    assert len(v) == len(w)
    f = w[0] / v[0]
    for i in range(len(v)):
        if abs(v[i] * f - w[i]) > EPSILON:
            return None
    return f

#   @ {U1:V1} =? s{U2:V2} tests if L1 = {U1:V1} equals L2 = {U2:V2}.
def line_equals(uv1, uv2)
    (u1, v1) = uv1
    (u2, v2) = uv2
    f = solve_scale(u1, v1)
    g = solve_scale(u2, v2)
    if not f or not g: return False
    return abs(f - g) < EPSILON

#   @ s > 0 if L1 and L2 have same orientation.
#   @ (V.V)/(U.U) is the minimum squared distance of L from the origin.
def distsq_from_origin(l):
    (u, v) = l
    return dot(v, v) / dot(u, u)

#   @ (VxU:U.U) is the point of L closest to the origin.
def point_closest_to_origin(l):
    (u, v) = l
    return mkhomo(cross(v, u), dot(u, u)) # homogeneous
#   @ [UxV:V.V] is the plane through L perpendicular to its origin plane, for
#         non-null V.
#   @ (VxN-Un:U.N) is the point where L intersects plane [N:n] not parallel to L.
#   @ [UxP-Vw:V.P] is the plane containing L and point (P:w) not on L.
#   @ [UxN:V.N] is the plane containing L and direction N not parallel to L.
#   Let N, N1, N2 be unit vectors along the coordinate axes, with U.N non-zero.
#   @ (VxN:U.N) is a point on L if N is not perpendicular to U.
#   @ U and this point both satisfy a plane equation [E:e] if the plane
#         contains L.
#   @ Represent L as U and this point to transform by non-perspective
#         homogeneous matrix.
#   @ Represent L as two points to transform by perspective homogeneous matrix.
#   @ [UxN1:V.N1] and [UxN2:V.N2] are distinct planes containing L.
#   @ P satisfies both these plane equations if L contains P.
#   @ Pnt(t) = (VxU+tU:U.U) parameterizes points on L.
#   @ Pln(t) = (1-t^2)[UxN1:V.N1]+2t[UxN2:V.N2] parameterizes planes through L.
#   @ U1.V2 + U2.V1 =? 0 tests if L1 = {U1:V1} and L2 = {U2:V2} are coplanar
#         (intersect).
#   @ Sum positive if right-handed screw takes one into the other; negative
#         if left-handed.
#   @ U1xU2 =? 0 tests if lines are parallel.
#   Let N be a unit vector along a coordinate axis, with (U1xU2).N non-zero.
#   @ ((V1.N)U2-(V2.N)U1-(V1.U2)N:(U1xU2).N) is the point of intersection, if
#         any.
#   @ [U1xU2:V1.U2] is the common plane for non-parallel lines.
#   Let N, N1, N2 be unit vectors along the coordinate axes, with U1.N non-zero.
#   @ [(U1.N)V2-(U2.N)V1:(V1xV2).N] is the common plane for parallel distinct
#         lines.
#   @ [U1xN1:V1.N1] is the common plane for equal lines through origin.

# Notes:

#   [Px Qx] row x
#   [Py Qy] row y
#   [Pz Qz] row z
#   [Pw Qw] row w
# Make all possible determinants of pairs of rows. Only six combinations are
# independent; these are the Plücker coordinates. See geometry yet? Probably not.
# But set the w's to 1, and look again.


