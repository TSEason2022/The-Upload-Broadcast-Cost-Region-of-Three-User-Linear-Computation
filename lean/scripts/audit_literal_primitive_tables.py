#!/usr/bin/env python3
"""Exact source transcription and rational diagnostics; Lean supplies the proof.
Requires SymPy. The source SHA-256 is authenticated before parsing its table cells.
"""
import sympy as s
from itertools import combinations

def es(n): return [s.eye(n)[:,i] for i in range(n)]
def mat(v,n): return s.Matrix.hstack(*v) if v else s.zeros(n,0)
e=es(5); a,b,c,d,f=e
Tside=[[a,d],[b,f],[c,d+f]]
D={
'T1':(Tside,[[b+f,c-f],[a+c+d],[a+b]]),
'T2':(Tside,[[b,c],[a,c+d],[a+b]]),
'T3':([Tside[0],Tside[2],Tside[1]],[[b+f,c+f],[a,b],[a+c,d]])}
e=es(4);a,b,c,d=e
D.update({'R1':([[d],[a,c],[b,c+d]],[[a,b],[b+d],[a+d]]),
'R2':([[a,b],[c,d],[a+c,b+d]],[[c+d],[b],[a]])})
e=es(3);a,b,c=e
D.update({'O':([[c],[a],[a+c,b]],[[b],[b+c],[]]), 'H':([[c],[a],[a+c,b]],[[b],[b+c],[a]])})
forms={'T1/2':[[1,0,0,-1,0]],'T1/3':[[0,0,0,1,-1]],'T2/3':[[1,-1,0,-1,1]],'T3/2':[[0,0,0,1,-1]],'R1/1':[[0,0,1,0]],'R2':[[0,0,1,-1],[1,0,0,0]],'O/1':[[1,0,0]],'O/2':[[0,1,-1]],'O/3':[[1,0,-1]],'H/1':[[1,0,0]]}
def canon(M): return M.columnspace() and s.Matrix.hstack(*M.columnspace()) or s.zeros(M.rows,0)
def null(M): return mat(M.nullspace(),M.cols)
def meet(A,B): return canon(A*null(A.row_join(-B))[:A.cols,:])
def crk(A,B): return A.row_join(B).rank()-B.rank()
def audit(A,U,P):
 d=P.rank(); a=[M.rank() for M in A]; u=[M.rank() for M in U]; m=[y-x for x,y in zip(a,u)]; t=sum(u)-2*d
 checks={}
 checks['side_span']=s.Matrix.hstack(*A).rank()==d
 checks['disjoint']=all(meet(A[i],A[j]).cols==0 for i,j in combinations(range(3),2))
 checks['pair_span']=all(U[i].row_join(U[j]).rank()==d for i,j in combinations(range(3),2))
 checks['triple_join']=meet(U[0],U[1]).row_join(U[2]).rank()==d
 checks['pair_crk']=all(crk(meet(U[i],U[j]),A[j])==min(m[j],u[i]+u[j]-d) for i in range(3) for j in range(3) if i!=j)
 tr=meet(meet(U[0],U[1]),U[2]); checks['triple_crk']=all(crk(tr,A[i])==min(m[i],t) for i in range(3))
 checks['t_bounds']=0<=t<=min(m)
 return d,a,u,t,checks
# This parser independently checks every copied coordinate against the frozen LaTeX.
def check_frozen_source(path=None):
    from pathlib import Path
    import hashlib,re
    path=Path(path) if path else Path(__file__).resolve().parents[2]/'source'/'TIT_LCBC_optimized.tex'
    text=path.read_text()
    assert hashlib.sha256(path.read_bytes()).hexdigest()=='b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682'
    def block(label):
        part=text.split('\\label{'+label+'}',1)[1]
        return part.split('\\midrule',1)[1].split('\\bottomrule',1)[0]
    def row_expr(expr,n):
        expr=expr.strip().strip('$').strip()
        if expr=='---':return []
        result=[]
        for v in expr.split(','):
            terms=re.findall(r'([+-]?)\s*\\mathbf e_([1-9])(?:\^\*)?',v)
            residue=re.sub(r'([+-]?)\s*\\mathbf e_([1-9])(?:\^\*)?','',v).strip()
            assert terms and not residue,(v,residue)
            col=s.zeros(n,1)
            for sign,i in terms:col[int(i)-1]+= -1 if sign=='-' else 1
            result.append(col)
        return result
    families={}
    for row in re.split(r'\\\\(?:\[2pt\])?',block('tab:primitive-flags')):
        if not row.strip():continue
        fields=[v.strip() for v in row.split('&')]
        name=fields[0].strip('$').replace('_','');n=int(fields[1])
        vals=[row_expr(v,n) for v in fields[2:]]
        assert len(vals)==6
        families[name]=(vals[:3],vals[3:])
    assert families==D,'literal flag transcription differs from frozen LaTeX'
    relays={}
    for row in re.split(r'\\\\',block('tab:primitive-relays')):
        if not row.strip():continue
        name,values=[v.strip().strip('$') for v in row.split('&')]
        name=name.replace('_','');n=D[name.split('/')[0]][0][0][0].rows
        relays[name]=[list(v) for v in row_expr(values.replace('\\ ',''),n)]
    assert relays==forms,'literal relay transcription differs from frozen LaTeX'
    return families,relays

if __name__=='__main__':
    check_frozen_source()
    for name,fs in forms.items():
        As,Bs=D[name.split('/')[0]]; n=As[0][0].rows
        A=[mat(x,n) for x in As]; U=[mat(x+y,n) for x,y in zip(As,Bs)]
        L=s.Matrix(fs); P=null(L)
        AP=[meet(P,x) for x in A]; UP=[meet(P,x) for x in U]
        full=audit(A,U,s.eye(n)); induced=audit(AP,UP,P)
        local=s.Matrix.hstack(*AP).rank()==P.rank()
        feasible=all(A[i].row_join(P).rank()==A[i].row_join(P).row_join(U[i]).rank() for i in range(3))
        assert all(full[-1].values()),(name,'full',full)
        assert all(induced[-1].values()),(name,'induced',induced)
        assert local and feasible,(name,local,feasible)
        print(name, 'full',full)
        print(' induced',induced,'local',local,'feasible',feasible)

    print('PASS: all seven flag rows and ten relay rows match the frozen source byte hash and parsed coordinates.')
