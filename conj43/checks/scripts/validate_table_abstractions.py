"""Validate the exact NL-abstraction of the 28 verdict lemmas + move lemma +
fixed/identity-case lemmas, exhaustively over the HYPOTHESIS POOLS (not just
real windows) -- this is what Lean's omega must prove."""
import itertools, sys

def step(m, a, b): return (b + m - a) % m
def cw4(m, a, b, c, d):
    s1, s2, s3, s4 = step(m,a,b), step(m,b,c), step(m,c,d), step(m,d,a)
    return s1>0 and s2>0 and s3>0 and s4>0 and s1+s2+s3+s4 == m

fails = []
def chk(name, cond):
    if not cond: fails.append(name)

# ---- A>b verdict pools: exhaustive n<=8 ----
cnt = 0
for n in range(2, 9):
    m = 2*n
    for a in range(n):
        for b in range(a+1, n):
            for A in range(b+1, a+n):        # b < A < a+n
                for B in range(A+1, min(b+n, a+n+1)):  # A < B < b+n, B <= a+n
                    al = A if A < n else A - n
                    be = B if B < n else B - n
                    for c in list(range(0, a)) + list(range(b+1, n)):
                        S = c + n if c < a else c
                        cnt += 1
                        # shared {al,be} verdicts
                        chk("w_ab_T", cw4(m, 2*a+1, 2*b+1, 2*al, 2*be))
                        chk("w_ba_F", not cw4(m, 2*b+1, 2*a+1, 2*be, 2*al))
                        chk("g_ab_F", not cw4(m, 2*b+1, 2*a+1, 2*al, 2*be))
                        chk("g_ba_F", not cw4(m, 2*a+1, 2*b+1, 2*be, 2*al))
                        # {al,b} points: w: e_al=2a+1 / g: e_al=2b+1; e_b=2c+1; x_al=2al, x_b=2b
                        w_alb = cw4(m, 2*a+1, 2*c+1, 2*al, 2*b)
                        w_bal = cw4(m, 2*c+1, 2*a+1, 2*b, 2*al)
                        g_alb = cw4(m, 2*b+1, 2*c+1, 2*al, 2*b)
                        g_bal = cw4(m, 2*c+1, 2*b+1, 2*b, 2*al)
                        # {be,b}: w: e_be=2b+1 / g: e_be=2a+1
                        w_beb = cw4(m, 2*b+1, 2*c+1, 2*be, 2*b)
                        w_bbe = cw4(m, 2*c+1, 2*b+1, 2*b, 2*be)
                        g_beb = cw4(m, 2*a+1, 2*c+1, 2*be, 2*b)
                        g_bbe = cw4(m, 2*c+1, 2*a+1, 2*b, 2*be)
                        if S < A:      # LEFT
                            chk("L", (not w_alb) and (not w_bal) and g_alb and (not g_bal)
                                and w_beb and (not w_bbe) and (not g_beb) and (not g_bbe))
                        elif S < B:    # TRIANGLE
                            chk("T", (not w_alb) and w_bal and (not g_alb) and (not g_bal)
                                and w_beb and (not w_bbe) and (not g_beb) and (not g_bbe))
                        else:          # RIGHT
                            chk("R", (not w_alb) and w_bal and (not g_alb) and (not g_bal)
                                and (not w_beb) and (not w_bbe) and (not g_beb) and g_bbe)
print("A>b verdict pool tuples:", cnt, "fails:", sorted(set(fails)) or 0)

# ---- identity-case (A=b) pools ----
fails2 = []
def chk2(name, cond):
    if not cond: fails2.append(name)
cnt2 = 0
for n in range(2, 9):
    m = 2*n
    for a in range(n):
        for b in range(a+1, n):
            for B in range(b+1, a+n+1):  # b < B <= a+n (< b+n auto)
                be = B if B < n else B - n
                cnt2 += 1
                # (b,be)/(be,b) in w: e_b=2a+1, e_be=2b+1, x_b=2b, x_be=2be
                chk2("id_bbe_F", not cw4(m, 2*a+1, 2*b+1, 2*b, 2*be))
                chk2("id_beb_F", not cw4(m, 2*b+1, 2*a+1, 2*be, 2*b))
                # (b,q)/(q,b) active q: s<a or b<s ; q<=a or b<q
                for s in list(range(0,a)) + list(range(b+1,n)):
                    for q in list(range(0,a+1)) + list(range(b+1,n)):
                        chk2("id_bq_F", not cw4(m, 2*a+1, 2*s+1, 2*b, 2*q))
                        chk2("id_qb_F", not cw4(m, 2*s+1, 2*a+1, 2*q, 2*b))
print("A=b pool tuples:", cnt2, "fails:", sorted(set(fails2)) or 0)

# ---- move lemma: m<=14, x<=x', stationary strictly avoid [x,x'] ----
fails3 = 0; cnt3 = 0
for mm in range(2, 15):
    for x in range(mm):
        for xp in range(x, mm):
            out = list(range(0,x)) + list(range(xp+1,mm))
            for c in out:
                for d in out:
                    for e in out:
                        cnt3 += 1
                        if cw4(mm,x,c,d,e) != cw4(mm,xp,c,d,e): fails3 += 1
print("move-lemma tuples:", cnt3, "fails:", fails3)

# ---- fixed-label + self lemmas ----
fails4 = 0; cnt4 = 0
for n in range(1, 8):
    m = 2*n
    for q in range(n):
        for sp in range(n):
            for p in range(n):
                cnt4 += 1
                if cw4(m, 2*sp+1, 2*q+1, 2*p, 2*q): fails4 += 1   # fixed snd
                if cw4(m, 2*q+1, 2*sp+1, 2*q, 2*p): fails4 += 1   # fixed fst
print("fixed-label tuples:", cnt4, "fails:", fails4)
print("ALL DONE")
