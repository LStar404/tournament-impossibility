#!/usr/bin/env python3
"""Fresh direct-Lean compilation and kernel inventory/axiom audit, no reused project objects."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path);p.add_argument('--check-sources-only',action='store_true');a=p.parse_args()
 manifest=json.loads((ROOT/'lean/verification557/sources.json').read_text());mods={r['module']:r for r in manifest['modules']}
 assert len(mods)==557
 for r in mods.values(): assert digest(ROOT/r['path'])==r['sha256'],r['path']
 for n,h in manifest['configuration'].items(): assert digest(ROOT/'lean'/n)==h,n
 if a.check_sources_only: print('557 source hashes and all configuration hashes match');return
 assert a.output,'Supply --output pointing to a new directory'
 out=a.output.resolve();out.mkdir(exist_ok=False);objects=out/'objects';objects.mkdir();audits=out/'audits';audits.mkdir()
 lean=os.environ.get('LEAN_BIN') or shutil.which('lean');assert lean,'Lean must be on PATH (or set LEAN_BIN)'
 version=subprocess.check_output([lean,'--version'],text=True);assert '4.35.0' in version,version
 packages=pathlib.Path(os.environ.get('MATHLIB_PACKAGES',ROOT/'lean/.lake/packages')).resolve();assert packages.is_dir()
 pins=json.loads((ROOT/'lean/lake-manifest.json').read_text())
 for r in pins['packages']:
  if r.get('type')=='git': assert subprocess.check_output(['git','-C',str(packages/r['name']),'rev-parse','HEAD'],text=True).strip()==r['rev'],r['name']
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[objects,*sorted(x/'.lake/build/lib/lean' for x in packages.iterdir() if x.is_dir())]))
 def run(args,cwd,log):
  with log.open('w') as f: subprocess.run([lean,*args],cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
 order=[];pending=set(mods)
 while pending:
  ready=sorted(n for n in pending if not(set(mods[n]['imports'])&pending));assert ready,'Cyclic imports'
  for n in ready:
   obj=objects/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
   run(['-o',str(obj),str(ROOT/mods[n]['path'])],ROOT/'lean',out/(n+'.compile.log'));print('Compiled',n,flush=True)
  order+=ready;pending.difference_update(ready)
 helper=ROOT/'tools/FullTreeAuditSupportFast.lean';run(['-o',str(objects/'FullTreeAuditSupportFast.olean'),str(helper)],helper.parent,out/'helper.log')
 driver=out/'Audit.lean';inv=out/'inventory.json'
 driver.write_text('\n'.join(['import FullTreeAuditSupportFast',*('import '+n for n in order),'set_option pp.fullNames true','set_option pp.universes true','set_option pp.explicit true','set_option pp.notation false','set_option pp.deepTerms true','set_option pp.maxSteps 1000000','#verify_full_tree_inventory ['+', '.join(order)+'] to '+json.dumps(str(inv)),*('#fast_full_tree_audit '+n+' to '+json.dumps(str(audits/(n+'.json'))) for n in order)])+'\n')
 run([str(driver)],out,out/'audit.log');inventory=json.loads(inv.read_text());assert inventory['all_match'] and inventory['module_count']==557
 by={r['module']:r for r in inventory['modules']};allowed={'propext','Classical.choice','Quot.sound'};total=0
 for n in order:
  d=json.loads((audits/(n+'.json')).read_text());rows=d['records'];assert d['environment_constant_count']==len(rows)
  assert len({r['name'] for r in rows})==len(rows);assert set(by[n]['kernel_names'])=={r['name'] for r in rows}
  assert all(r['module']==n and r['builtin_check_and_print_axioms_invoked'] and set(r['axioms'])<=allowed for r in rows)
  assert digest(ROOT/mods[n]['path'])==mods[n]['sha256'];total+=len(rows)
 assert total==7907,total
 (out/'result.json').write_text(json.dumps({'passed':True,'modules':557,'declarations':total,'allowed_axioms':sorted(allowed),'reused_project_objects':0},indent=2)+'\n');print('PASS: 557 modules, 7907 declarations')
if __name__=='__main__':main()
