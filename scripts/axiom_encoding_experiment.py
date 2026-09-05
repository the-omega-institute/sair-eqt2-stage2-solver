import json,sys,glob,ast,re
sys.path.insert(0,'/Users/lexa/Desktop/lexa/omega/eqt2-stage2')
from judge.verify import verify_answer
src=open('/Users/lexa/Desktop/lexa/omega/eqt2-stage2/pipeline/proxy.py').read()
m=re.search(r'DEFAULT_PROOF_POLICY\s*=\s*(\{.*?\n\})',src,re.S)
OFFICIAL=ast.literal_eval(m.group(1))
ZERO={**OFFICIAL,'allowed_axioms':[]}
idx={}
for f in glob.glob('/Users/lexa/Desktop/lexa/omega/eqt2-stage2/examples/problems/**/*',recursive=True):
    if not f.endswith(('.jsonl','.json')): continue
    try:
        txt=open(f).read()
        rows=[json.loads(l) for l in txt.splitlines() if l.strip().startswith('{')] if f.endswith('.jsonl') else (json.loads(txt) if txt.strip().startswith('[') else [])
    except Exception: continue
    for r in rows:
        if isinstance(r,dict) and 'equation1' in r: idx[(r['eq1_id'],r['eq2_id'])]=r
cands=json.load(open('/tmp/affine_cands.json'))
out=[]; done=0
def run(prob,code,enc,cid,policy,pname,n):
    p=dict(prob); p['proof_policy']=policy
    try: res=verify_answer(p,json.dumps({"verdict":"false","code":code}))
    except Exception as e: return {'cert':cid,'enc':enc,'policy':pname,'carrier':n,'status':'ERROR','axioms':[],'err':str(e)[:100]}
    return {'cert':cid,'enc':enc,'policy':pname,'carrier':n,'status':res.get('status'),'axioms':sorted(res.get('axioms') or [])}
for c in cands:
    prob=idx.get((c['eq1'],c['eq2']))
    if prob is None: continue
    n=c['n']; a,b,k=c['coef']
    ar=(f"import JudgeProblem\nimport JudgeDecide.DecideBang\n\nnamespace submission\n"
        f"def op (x y : Fin {n}) : Fin {n} := ⟨({a} * x.val + {b} * y.val + {k}) % {n}, Nat.mod_lt _ (by decide)⟩\n"
        f"end submission\n\nset_option maxRecDepth 1000000 in\nset_option maxHeartbeats 1000000 in\n"
        f"def submission : Goal := by\n  let m : Magma (Fin {n}) := {{ op := submission.op }}\n"
        f"  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n")
    for enc,code in (('finOpTable',c['code']),('arithmetic',ar)):
        out.append(run(prob,code,enc,c['id'],OFFICIAL,'official',n))
        out.append(run(prob,code,enc,c['id'],ZERO,'zero-axiom',n))
    done+=1; print(f"{done} {c['id']} Fin{n}",flush=True)
    json.dump(out,open('/tmp/axresults2.json','w'),indent=1)
print('DONE',done,len(out))
