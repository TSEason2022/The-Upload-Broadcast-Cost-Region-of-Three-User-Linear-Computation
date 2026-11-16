#!/usr/bin/env python3
"""Regenerate literal integer certificates; generation is not part of the trust base.
Lean checks every emitted equality with ordinary `decide`, then derives actual
field-uniform subspace ranks. Requires SymPy only for optional regeneration.
"""
import sys,itertools,sympy as s
import argparse, os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT)
parser=argparse.ArgumentParser()
parser.add_argument('--check',action='store_true',help='compare generated files without modifying them')
args=parser.parse_args()
sys.path.insert(0,str(ROOT/'scripts'))
def save(path,content):
 if args.check:
  assert path.read_text()==content,f'generated certificate differs: {path}'
 elif not path.exists() or path.read_text()!=content:path.write_text(content)
from audit_literal_primitive_tables import D, forms,mat, null,meet, canon, check_frozen_source
check_frozen_source()

def ann(M):return null(M.T).T

def fmt(M):
 assert all(x.q == 1 for x in M), M
 if M.rows==0:return '(fun i => Fin.elim0 i)'
 return '!['+', '.join(('!['+', '.join(str(int(x)) if x>=0 else f'({int(x)})' for x in M[i,:])+']') for i in range(M.rows))+']'

def coeff(B,M):
 r=B.rank()
 for I in itertools.combinations(range(B.rows),r):
  for J in itertools.combinations(range(B.cols),r):
   Q=B.extract(I,J)
   if abs(Q.det())==1:
    X=B[:,J];Y=Q.inv()*B[I,:];L=Q.inv()*s.eye(B.rows)[I,:];R=s.eye(B.cols)[:,J]
    assert X*Y==B
    C=R*Q.inv()*M[I,:];assert B*C==M
    return X,Y,L,R,C
 raise ValueError(B)
class Gen:
 def __init__(self):self.out=[];self.memo={};self.count=0
 def w(self,x=''):self.out.append(x)
 def define(self,name,M):self.w(f'def {name} : Matrix (Fin {M.rows}) (Fin {M.cols}) ℤ := {fmt(M)}');return name
 def rank(self,name,M):
  key=(name,tuple(M))
  if key in self.memo:return self.memo[key]
  self.count+=1;label=f'rank_{self.count}'; self.memo[key]=label;r=M.rank();X,Y,L,R,_=coeff(M,M)
  self.w(f'''lemma {label} : (castMatrix ({name}) : Matrix (Fin {M.rows}) (Fin {M.cols}) K).rank = {r} := by
  exact rank_int_certificate ({name})
    ({fmt(X)}) ({fmt(Y)}) ({fmt(L)}) ({fmt(R)}) (by decide) (by decide)
''');return label
 def dim(self,label,expr,Nname,N,n):
  rk=self.rank(Nname,N)
  rewrite='  repeat rw [kernel_stack] at h\n' if 'stack' in Nname else ''
  self.w(f'''lemma {label} : finrank K ↥({expr}) = {n-N.rank()} := by
  have h := kernel_finrank (K := K) ({Nname}) ({rk} (K := K))
{rewrite}  exact h
''');return n-N.rank()

g=Gen();g.w('''import UploadBroadcast.LiteralMatrixCertificates
/-! Literal base flags and relay forms, frozen source tables primitive-flags
and primitive-relays. Generated exact integer identities; all ranks and spaces
are certified uniformly over an arbitrary field, including characteristic two. -/
namespace UploadBroadcast.LiteralPrimitiveTables
open Matrix Module LiteralMatrixCertificates NonzeroDefectProfile
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]
''')
for cname,fs in forms.items():
 g.memo={};g.w('namespace '+cname.replace('/','_'))
 As,Bs=D[cname.split('/')[0]];n=As[0][0].rows;Us=[mat(a+b,n) for a,b in zip(As,Bs)];As=[mat(a,n) for a in As]
 Ns=list(map(ann,As+Us));L=s.Matrix(fs);P=null(L);AP=[meet(P,A) for A in As]
 g.define('relayForms',L);g.w(f'abbrev relay : Submodule K (Fin {n} → K) := kernel relayForms')
 rL=g.rank('relayForms',L);g.dim('dim_relay','relay (K := K)','relayForms',L,n)
 g.define('relayBasis',P);rP=g.rank('relayBasis',P)
 g.w(f'lemma relay_columns : columns (K := K) relayBasis = relay := columns_eq_kernel _ _ (by decide) ({rP} (K := K)) ({rL} (K := K)) (by decide)\n')
 an=[];un=[]
 for prefix,arr in [('side',[*As]),('signal',[*Us])]:
  for i,M in enumerate(arr):
   mn=g.define(prefix+str(i)+'Columns',M);N=ann(M);nn=g.define(prefix+str(i)+'Constraints',N)
   rM=g.rank(mn,M);rN=g.rank(nn,N)
   g.w(f'lemma {prefix}{i}_literal : columns (K := K) {mn} = kernel {nn} :=\n  columns_eq_kernel _ _ (by decide) ({rM} (K := K)) ({rN} (K := K)) (by decide)\n')
   (an if prefix=='side' else un).append(nn)
 for i,B in enumerate(Bs):
  BM=mat(B,n);g.define(f'demand{i}Columns',BM)
  g.w(f'lemma signal{i}_from_demands : signal{i}Columns = joinColumns side{i}Columns demand{i}Columns := by decide\n')
 g.w(f'def side : Three → Submodule K (Fin {n} → K) := !['+', '.join('kernel '+x for x in an)+']')
 g.w(f'def signal : Three → Submodule K (Fin {n} → K) := !['+', '.join('kernel '+x for x in un)+']\n')
 g.w('lemma side_le_signal (i : Three) : side (K := K) i ≤ signal i := by\n  fin_cases i')
 for i in range(3):
  C=coeff(Us[i],As[i])[4]
  g.w(f'  · change kernel {an[i]} ≤ kernel {un[i]}\n    rw [← side{i}_literal, ← signal{i}_literal]\n    exact columns_le_columns _ _ ({fmt(C)}) (by decide)')
 fulljoin='joinColumns (joinColumns side0Columns side1Columns) side2Columns';fullmat=s.Matrix.hstack(*As);rf=g.rank(fulljoin,fullmat)
 g.w(f'''lemma side_spanning : (⨆ i, side (K := K) i) = ⊤ := by
  have h := columns_eq_top (K := K) ({fulljoin}) ({rf} (K := K))
  simpa only [columns_join, side0_literal, side1_literal, side2_literal,
    Profile.three_iSup, side, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, sup_assoc] using h
''')
 g.w(f'''def task : Task K (Fin {n} → K) where
  A := side
  U := signal
  side_le_signal := side_le_signal
  feasible i := by rw [side_spanning]; exact le_top
''')
 for i,M in enumerate(AP):
  name=g.define('inducedSide'+str(i)+'Columns',M);rm=g.rank(name,M);nn=f'stack relayForms {an[i]}';N=L.col_join(Ns[i]);rn=g.rank(nn,N)
  g.w(f'''lemma inducedSide{i}_literal : columns (K := K) {name} = relay ⊓ side {i} := by
  have h := columns_eq_kernel (K := K) {name} ({nn}) (by decide) ({rm} (K := K)) ({rn} (K := K)) (by decide)
  simpa only [kernel_stack, side, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h
''')
 ij='joinColumns (joinColumns inducedSide0Columns inducedSide1Columns) inducedSide2Columns';IM=s.Matrix.hstack(*AP);ri=g.rank(ij,IM)
 g.w(f'''lemma locally_generated : (task (K := K)).LocallyGenerated relay := by
  have h : columns (K := K) ({ij}) = ⨆ i, relay ⊓ side i := by
    simp only [columns_join, inducedSide0_literal, inducedSide1_literal,
      inducedSide2_literal, Profile.three_iSup, sup_assoc]
  unfold Task.LocallyGenerated
  change relay = ⨆ i, relay ⊓ side i
  symm
  apply Submodule.eq_of_le_of_finrank_eq (iSup_le fun i => inf_le_left)
  rw [← h, columns_finrank, {ri}, dim_relay]
''')
 g.w('lemma relay_feasible : (task (K := K)).RelayFeasible relay := by\n  intro i\n  fin_cases i')
 for i in range(3):
  N=As[i].row_join(P);C=coeff(N,Us[i])[4]
  g.w(f'''  · change kernel {un[i]} ≤ kernel {an[i]} ⊔ relay
    rw [← side{i}_literal, ← signal{i}_literal, ← relay_columns, ← columns_join]
    exact columns_le_columns _ _ ({fmt(C)}) (by decide)''')
 g.w(f'''def inducedTask : Task K (Fin {n} → K) where
  A i := relay ⊓ side i
  U i := relay ⊓ signal i
  side_le_signal i := inf_le_inf_left _ (side_le_signal i)
  feasible i := by
    change relay ⊓ signal i ≤ ⨆ j, relay ⊓ side j
    have h : relay (K := K) = ⨆ j, relay ⊓ side j := locally_generated
    rw [← h]
    exact inf_le_left
''')
 for mode in ['full','induced']:
  def expr(prefix,i):return f'kernel (K := K) {prefix}{i}Constraints' if mode=='full' else f'relay (K := K) ⊓ kernel {prefix}{i}Constraints'
  def cons(prefix,i):
   j=i if prefix=='side' else i+3
   return (f'{prefix}{i}Constraints',Ns[j]) if mode=='full' else (f'stack relayForms {prefix}{i}Constraints', L.col_join(Ns[j]))
  def inter(items):
   en,ma=cons(*items[0]);ex=expr(*items[0])
   for item in items[1:]:
    en2,ma2=cons(*item);en=f'stack ({en}) ({en2})';ma=ma.col_join(ma2);ex=f'({ex}) ⊓ ({expr(*item)})'
   return ex,en,ma
  for prefix in ['side','signal']:
   for i in range(3):
    ex,en,ma=inter([(prefix,i)]);g.dim(f'{mode}_{prefix}{i}_dim',ex,en,ma,n)
  for i,j in itertools.combinations(range(3),2):
   ex,en,ma=inter([('signal',i),('signal',j)]);g.dim(f'{mode}_pair{i}{j}_dim',ex,en,ma,n)
  ex,en,ma=inter([('signal',0),('signal',1),('signal',2)]);g.dim(f'{mode}_triple_dim',ex,en,ma,n)
  for i in range(3):
   for j in range(3):
    if i==j:continue
    ex,en,ma=inter([('side',j),('signal',i)]);g.dim(f'{mode}_sideSignal{j}{i}_dim',ex,en,ma,n)
  for i in range(3):
   ex,en,ma=inter([('signal',0),('signal',1),('signal',2),('side',i)]);g.dim(f'{mode}_tripleSide{i}_dim',ex,en,ma,n)
  aa=[A.cols for A in As] if mode=='full' else [A.cols for A in AP]
  uu=[U.cols for U in Us] if mode=='full' else [meet(P,U).cols for U in Us]
  tn='task' if mode=='full' else 'inducedTask';vn='⊤' if mode=='full' else 'relay'
  simpbase=f'{tn}, side, signal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two'
  dimnames=[f'{mode}_{p}{i}_dim' for p in ['side','signal'] for i in range(3)]+[f'{mode}_pair{i}{j}_dim' for i,j in itertools.combinations(range(3),2)]+[f'{mode}_triple_dim']+[f'{mode}_sideSignal{j}{i}_dim' for i in range(3) for j in range(3) if i!=j]+[f'{mode}_tripleSide{i}_dim' for i in range(3)]
  simpdim=', '.join(dimnames)+', dim_relay, finrank_top, finrank_pi, Fintype.card_fin'
  g.w(f"theorem {mode}_rankConditions : RankConditions ({tn} (K := K)) {vn}\n    ![{','.join(map(str,aa))}] ![{','.join(map(str,uu))}] := by\n  apply rankConditions_in_ambient")
  g.w(f"  · intro i; exact {'le_top' if mode=='full' else 'inf_le_left'}")
  for pre in ['side','signal']:
   g.w('  · intro i; fin_cases i')
   for i in range(3):g.w(f'    · exact {mode}_{pre}{i}_dim')
  g.w('  · intro i j hij; fin_cases i <;> fin_cases j')
  for i in range(3):
   for j in range(3):
    if i==j:g.w('    · exact (hij rfl).elim');continue
    ex,en,ma=inter([('signal',i),('signal',j)])
    g.w(f'    · change finrank K ↥({ex}) + finrank K ↥({vn} : Submodule K (Fin {n} → K)) = {uu[i]+uu[j]}')
    if i>j:g.w('      rw [inf_comm]')
    g.w(f'      rw [{mode}_pair{min(i,j)}{max(i,j)}_dim]')
    g.w('      norm_num [dim_relay, finrank_top, finrank_pi]')
  ex,en,ma=inter([('signal',0),('signal',1),('signal',2)])
  g.w(f'  · change finrank K ↥({ex}) + 2 * finrank K ↥({vn} : Submodule K (Fin {n} → K)) = {sum(uu)}')
  g.w(f'    rw [{mode}_triple_dim]; norm_num [dim_relay, finrank_top, finrank_pi]')
  g.w('  · intro i j hij; fin_cases i <;> fin_cases j')
  for i in range(3):
   for j in range(3):
    if i==j:g.w('    · exact (hij rfl).elim');continue
    ex,en,ma=inter([('side',j),('signal',i)])
    g.w(f'    · change finrank K ↥({ex}) = {aa[j]+uu[i]} - finrank K ↥({vn} : Submodule K (Fin {n} → K))')
    g.w(f'      rw [{mode}_sideSignal{j}{i}_dim]; norm_num [dim_relay, finrank_top, finrank_pi]')
  g.w('  · intro i; fin_cases i')
  for i in range(3):g.w(f'    · exact {mode}_tripleSide{i}_dim')
  fp=[max(uu[i]-aa[i], (n if mode=='full' else P.cols)-aa[i]-aa[j]) for i,j in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]]
  dq=sum(uu[i]-aa[i] for i in range(3))-(sum(uu)-2*(n if mode=='full' else P.cols))
  g.w(f"\ntheorem {mode}_first_profile (r : Fin 6) : Profile.entry ({tn} (K := K)) (.inl r) = ![{','.join(map(str,fp))}] r := by")
  g.w(f"  change Profile.firstEntry _ (Profile.firstOrder r).1 (Profile.firstOrder r).2.1 (Profile.firstOrder r).2.2 = _")
  g.w(f"  rw [firstEntry_max _ _ _ _ {mode}_rankConditions _ _ _ (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide)]")
  g.w('  fin_cases r <;> norm_num [Profile.firstOrder, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]')
  g.w(f"\ntheorem {mode}_second_profile (i ell : Three) : 2 * Profile.entry ({tn} (K := K)) (.inr (i,ell)) = {dq} := by")
  g.w(f"  change 2 * Profile.secondEntry _ i (i+1) (i+2) ell = _")
  g.w(f"  rw [secondEntry_formula _ _ _ _ {mode}_rankConditions _ _ _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]")
  g.w('  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]')
 # post-process placeholder side dims explicit cases
 text='\n'.join(g.out)
 # do later
 # The common kernel of the side-sum matrix is the actual relation coordinate space.
 Rel=null(fullmat);g.define('relationBasis',Rel);rr=g.rank('relationBasis',Rel)
 g.w(f"lemma relation_space : columns (K := K) relationBasis = kernel ({fulljoin}) :=\n  columns_eq_kernel _ _ (by decide) ({rr} (K := K)) ({rf} (K := K)) (by decide)\n")
 offset=0; vals=[];Rs=[]
 for i in range(3):
  sl=Rel[offset:offset+As[i].cols,:];comp=As[i]*sl;offset+=As[i].cols;Rs.append(comp)
  g.define(f'relationSlice{i}',sl)
  name=g.define(f'relationComponent{i}',comp);val=L*comp;vals.append(val)
  g.w(f'lemma relationComponent{i}_from_side : side{i}Columns * relationSlice{i} = relationComponent{i} := by decide\n')
  g.w(f'lemma relationComponent{i}_in_side : columns (K := K) relationComponent{i} ≤ side {i} := by\n  change columns (K := K) relationComponent{i} ≤ kernel side{i}Constraints\n  rw [← side{i}_literal]\n  exact columns_le_columns _ _ relationSlice{i} relationComponent{i}_from_side\n')
  g.w(f"lemma relation_value{i} : (castMatrix relayForms : Matrix (Fin {L.rows}) (Fin {n}) K) * castMatrix {name} = castMatrix ({fmt(val)} : Matrix (Fin {L.rows}) (Fin {Rel.cols}) ℤ) := by\n  have h : relayForms * {name} = ({fmt(val)} : Matrix (Fin {L.rows}) (Fin {Rel.cols}) ℤ) := by decide\n  simpa only [castMatrix, ← Matrix.map_mul] using congrArg (fun M => M.map (Int.castRingHom K)) h\n")
 g.w('lemma relation_slices_partition : stack (stack relationSlice0 relationSlice1) relationSlice2 = relationBasis := by decide\n')
 g.w(f"lemma relation_sum : (castMatrix relationComponent0 : Matrix (Fin {n}) (Fin {Rel.cols}) K) + castMatrix relationComponent1 + castMatrix relationComponent2 = 0 := by\n  ext i j; fin_cases i <;> fin_cases j <;> norm_num [castMatrix, relationComponent0, relationComponent1, relationComponent2]\n")
 if cname=='R2':
  W=s.Matrix.vstack(vals[1][0,:],vals[0][1,:]);g.define('wedgeMatrix',W)
  g.w('lemma wedge_from_relation_components : wedgeMatrix = ![(relayForms * relationComponent1) 0, (relayForms * relationComponent0) 1] := by decide\n')
  g.w("theorem wedge_determinant : (castMatrix wedgeMatrix : Matrix (Fin 2) (Fin 2) K).det = 1 := by\n  norm_num [Matrix.det_fin_two, castMatrix, wedgeMatrix]\n")
  for arm, word in [(0,'first'),(1,'second')]:
   g.w(f'def {word}RelayForm : Matrix (Fin 1) (Fin 4) ℤ := ![relayForms {arm}]\n')
   g.w(f'theorem {word}_form_signal_zero : (castMatrix {word}RelayForm : Matrix (Fin 1) (Fin 4) K) * (castMatrix signal{arm}Columns : Matrix (Fin 4) (Fin 3) K) = 0 := by\n  have h : {word}RelayForm * signal{arm}Columns = 0 := by decide\n  rw [castMatrix, castMatrix, ← Matrix.map_mul, h]\n  exact Matrix.map_zero _ (map_zero _)\n')
   g.w(f'theorem {word}_form_vanishes : signal (K := K) {arm} ≤ kernel {word}RelayForm := by\n  change kernel signal{arm}Constraints ≤ kernel {word}RelayForm\n  rw [← signal{arm}_literal]\n  apply LinearMap.range_le_ker_iff.mpr\n  rw [← Matrix.mulVecLin_mul, {word}_form_signal_zero, Matrix.mulVecLin_zero]\n')
  g.w('theorem actual_wedge_determinant : Matrix.det (![((castMatrix relayForms : Matrix (Fin 2) (Fin 4) K) * (castMatrix relationComponent1 : Matrix (Fin 4) (Fin 2) K)) 0, ((castMatrix relayForms : Matrix (Fin 2) (Fin 4) K) * (castMatrix relationComponent0 : Matrix (Fin 4) (Fin 2) K)) 1]) = 1 := by\n  norm_num [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ, castMatrix, relayForms, relationComponent1, relationComponent0]\n')
 else:
  arm=int(cname.split('/')[1])-1
  g.w(f"theorem relay_form_vanishes : signal (K := K) {arm} ≤ relay := by\n  change kernel {un[arm]} ≤ relay\n  rw [← signal{arm}_literal, ← relay_columns]\n  exact columns_le_columns _ _ ({fmt(coeff(P,Us[arm])[4])}) (by decide)\n")
 for i,j in itertools.combinations(range(3),2):
  nn=f'stack {an[i]} {an[j]}';N=Ns[i].col_join(Ns[j])
  g.dim(f'side_pair{i}{j}_dim', f'kernel (K := K) {an[i]} ⊓ kernel {an[j]}',nn,N,n)
 g.w('theorem side_pairwise_disjoint (i j : Three) (hij : i ≠ j) : Disjoint (side (K := K) i) (side j) := by\n  rw [disjoint_iff]\n  apply Submodule.finrank_eq_zero.mp\n  fin_cases i <;> fin_cases j')
 for i in range(3):
  for j in range(3):
   if i==j:g.w('  · exact (hij rfl).elim');continue
   if i>j:g.w(f'  · change finrank K ↥(kernel (K := K) {an[i]} ⊓ kernel {an[j]}) = 0\n    rw [inf_comm]; exact side_pair{j}{i}_dim')
   else:g.w(f'  · exact side_pair{i}{j}_dim')
 g.w('end '+cname.replace('/','_'))
g.w('end UploadBroadcast.LiteralPrimitiveTables')
out='\n'.join(g.out)
# replace using_assumption lines with first dims unfolding plus matching theorem simp
out=out.replace('simpa only [task, side, signal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using_assumption','simp only [task, side, signal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, full_side0_dim, full_side1_dim, full_side2_dim, full_signal0_dim, full_signal1_dim, full_signal2_dim]')
out=out.replace('simpa only [inducedTask, side, signal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using_assumption','simp only [inducedTask, side, signal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, induced_side0_dim, induced_side1_dim, induced_side2_dim, induced_signal0_dim, induced_signal1_dim, induced_signal2_dim]')
from pathlib import Path
header, rest=out.split('namespace T1_2',1)
rest='namespace T1_2'+rest
imports=[]
for cname in forms:
 name=cname.replace('/','_')
 start=rest.index('namespace '+name+'\n')
 end=rest.index('end '+name+'\n',start)+len('end '+name+'\n')
 body=rest[start:end]
 module='LiteralPrimitive'+name
 target=Path('UploadBroadcast')/(module+'.lean')
 save(target,header+body+'end UploadBroadcast.LiteralPrimitiveTables\n')
 imports.append('import UploadBroadcast.'+module)
save(Path('UploadBroadcast/LiteralPrimitiveTables.lean'),'\n'.join(imports)+'\n')
print(f'Generated {len(forms)} modules and {g.count} field-uniform rank certificates.')
