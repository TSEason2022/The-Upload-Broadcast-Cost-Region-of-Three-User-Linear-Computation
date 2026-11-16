#!/usr/bin/env python3
"""Independent transcription check only; mathematical ranks use Lean certificates."""
from pathlib import Path
import ast, hashlib, json, re
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT.parent/'source'/'TIT_LCBC_optimized.tex'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()=='b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682'
def e(n,i): return [int(j==i-1) for j in range(n)]
def add(*xs): return [sum(z) for z in zip(*xs)]
def neg(x): return [-z for z in x]
def columns(vs,n): return [list(z) for z in zip(*vs)] if vs else [[] for _ in range(n)]
def setup(n): return [None]+[e(n,i) for i in range(1,n+1)]
v=setup(5)
base5=[[v[1],v[4]],[v[2],v[5]],[v[3],add(v[4],v[5])]]
T1=(5,base5,[[add(v[2],v[5]),add(v[3],neg(v[5]))],[add(v[1],v[3],v[4])],[add(v[1],v[2])]])
T2=(5,base5,[[v[2],v[3]],[v[1],add(v[3],v[4])],[add(v[1],v[2])]])
T3=(5,[base5[0],base5[2],base5[1]],[[add(v[2],v[5]),add(v[3],v[5])],[v[1],v[2]],[add(v[1],v[3]),v[4]]])
v=setup(4)
R1=(4,[[v[4]],[v[1],v[3]],[v[2],add(v[3],v[4])]],[[v[1],v[2]],[add(v[2],v[4])],[add(v[1],v[4])]])
R2=(4,[[v[1],v[2]],[v[3],v[4]],[add(v[1],v[3]),add(v[2],v[4])]],[[add(v[3],v[4])],[v[2]],[v[1]]])
v=setup(3)
base3=[[v[3]],[v[1]],[add(v[1],v[3]),v[2]]]
O=(3,base3,[[v[2]],[add(v[2],v[3])],[]])
H=(3,base3,[[v[2]],[add(v[2],v[3])],[v[1]]])
cases={'T1_2':(T1,[[1,0,0,-1,0]]),'T1_3':(T1,[[0,0,0,1,-1]]),'T2_3':(T2,[[1,-1,0,-1,1]]),'T3_2':(T3,[[0,0,0,1,-1]]),'R1_1':(R1,[[0,0,1,0]]),'R2':(R2,[[0,0,1,-1],[1,0,0,0]]),'O_1':(O,[[1,0,0]]),'O_2':(O,[[0,1,-1]]),'O_3':(O,[[1,0,-1]]),'H_1':(H,[[1,0,0]])}
results=[]
for name,((n,A,B),forms) in cases.items():
    p=ROOT/'UploadBroadcast'/f'LiteralPrimitive{name}.lean'
    text=p.read_text()
    def get(label):
        match=re.search(r'^def '+label+r'\s*:[^\n]* := (.*)$',text,re.M)
        assert match, (name,label,'missing definition')
        return ast.literal_eval(match.group(1).replace('!',''))
    expectations={'relayForms':forms}
    for i in range(3):
        expectations[f'side{i}Columns']=columns(A[i],n)
        expectations[f'demand{i}Columns']=columns(B[i],n)
        expectations[f'signal{i}Columns']=columns(A[i]+B[i],n)
    for label,want in expectations.items():
        assert get(label)==want,(name,label,get(label),want)
    results.append({'case':name,'matched_matrices':list(expectations),'source':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
output={'description':'Exact integer transcription check against independently entered frozen tables, not a mathematical rank or Lean proof.','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'case_count':len(results),'matched_matrix_count':sum(len(x['matched_matrices']) for x in results),'passed':True,'cases':results}
(ROOT/'verification'/'literal-primitive-transcription-20261008.json').write_text(json.dumps(output,indent=2)+'\n')
print('PASS: all 100 literal matrices across 10 relay choices match the frozen primitive flag and relay tables.')
