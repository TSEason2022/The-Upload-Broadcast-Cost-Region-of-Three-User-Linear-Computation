#!/usr/bin/env python3
"""Exact symbolic companion check; the Lean proof supplies all-characteristic validity."""
import hashlib
import itertools
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / 'source' / 'TIT_LCBC_optimized.tex'
SOURCE_SHA256 = 'b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256
q = s.symbols('theta')

def mat(columns, d):
    return s.Matrix.hstack(*(s.Matrix(v) for v in columns)) if columns else s.zeros(d, 0)

def basis(M):
    return mat(M.columnspace(), M.rows)

def join(A, B):
    return basis(A.row_join(B))

def meet(A, B):
    return basis(mat([A * v[:A.cols, :] for v in A.row_join(-B).nullspace()], A.rows))

def cond(B, A):
    return join(A, B).rank() - A.rank()

def profile(A, U):
    demand = sum(u.rank() - a.rank() for a, u in zip(A, U))
    triple = meet(meet(U[0], U[1]), U[2])
    first = [demand - cond(meet(U[i], U[j]), A[j]) -
             cond(meet(U[k], join(U[i], U[j])), A[k])
             for i, j, k in itertools.permutations(range(3))]
    second2 = [2 * demand - cond(triple, A[e]) -
               cond(join(meet(U[i], U[(i+1)%3]), meet(U[i], U[(i+2)%3])), A[i]) -
               cond(meet(U[(i+1)%3], join(U[i], U[(i+2)%3])), A[(i+1)%3]) -
               cond(meet(U[(i+2)%3], join(U[i], U[(i+1)%3])), A[(i+2)%3])
               for i in range(3) for e in range(3)]
    assert first == [1]*6 and second2 == [3]*9
    assert triple.rank() == 0
    pair_dims = [meet(U[i],U[j]).rank() for i,j in itertools.combinations(range(3),2)]
    pair_cond = [cond(meet(U[i], U[j]), A[j]) for i,j in itertools.permutations(range(3),2)]
    assert pair_cond == [1]*6
    return dict(side_ranks=[a.rank() for a in A],signal_ranks=[u.rank() for u in U],
                pair_ranks=pair_dims,triple_rank=0,pair_conditional_ranks=pair_cond,
                first_six=first,doubled_second_nine=second2)

E = s.eye(4)
x,y,z,w = [E[:,i] for i in range(4)]
A = [mat([x],4),mat([y,w],4),mat([z,x+w],4)]
U = [mat([x,y+z],4),mat([y,x+z,w],4),mat([z,x+q*y,x+w],4)]
P = mat([x,y,z],4)
Ai,Ui = [meet(a,P) for a in A],[meet(u,P) for u in U]
report = {'source_sha256':SOURCE_SHA256,'coefficient_field':'Q(theta)',
          'R0_full':profile(A,U),'R0_relay':profile(Ai,Ui)}
assert report['R0_full']['pair_ranks'] == [1,1,2]
assert report['R0_relay']['pair_ranks'] == [1,1,1]
for i in range(3):
    assert join(A[i],P).rank() == join(join(A[i],P),U[i]).rank()
assert join(join(Ai[0],Ai[1]),Ai[2]).rank() == P.rank() == 3
A3 = [a[:3,:] for a in Ai]
U3 = [u[:3,:] for u in Ui]
report['D'] = profile(A3,U3)
print(json.dumps(report, indent=2))
