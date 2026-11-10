#!/usr/bin/env python3
"""Portable fresh 563-source build and full kernel audit.
This adapter's full build is separate from the recorded seven-module incremental
integration run. Existing project objects are never reused by this adapter.
"""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,tomllib
ROOT=pathlib.Path(__file__).resolve().parents[1]
def digest(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path);p.add_argument('--check-sources-only',action='store_true');a=p.parse_args()
 manifest=json.loads((ROOT/'lean/verification563/sources.json').read_text());mods={r['module']:r for r in manifest['modules']};assert len(mods)==563
 def inputs():
  for r in mods.values():assert digest(ROOT/r['path'])==r['sha256'],r['path']
  for n,h in manifest['configuration'].items():assert digest(ROOT/'lean'/n)==h,n
  for n,h in manifest['tooling'].items():assert digest(ROOT/n)==h,n
 config=tomllib.loads((ROOT/'lean/lakefile.toml').read_text());roots=[n for lib in config['lean_lib'] for n in lib['roots']];assert len(roots)==len(set(roots))==563 and set(roots)==set(mods)
 inputs()
 if a.check_sources_only:print('563 source hashes, all configuration and helper hashes match');return
 assert a.output,'Supply --output pointing to a new directory'
 out=a.output.resolve();out.mkdir(exist_ok=False)
 for d in ['objects','helpers','audits','exact_types','logs']:(out/d).mkdir()
 objects=out/'objects';lean=os.environ.get('LEAN_BIN') or shutil.which('lean');assert lean,'Set LEAN_BIN or put Lean on PATH'
 assert '4.35.0' in subprocess.check_output([lean,'--version'],text=True)
 packages=pathlib.Path(os.environ.get('MATHLIB_PACKAGES',ROOT/'lean/.lake/packages')).resolve();assert packages.is_dir()
 pins=json.loads((ROOT/'lean/lake-manifest.json').read_text());package_paths=[]
 for r in pins['packages']:
  assert r['type']=='git';p=packages/r['name'];assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==r['rev'],r['name']
  lib=p/'.lake/build/lib/lean';assert lib.is_dir();package_paths.append(lib)
  for n in mods:assert not(lib/(n.replace('.','/')+'.olean')).exists(),('project shadow',n,p)
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[objects,out/'helpers',*sorted(package_paths)]));(out/'LEAN_PATH').write_text(env['LEAN_PATH']+'\n')
 def run(args,cwd,log):
  with log.open('w') as f:subprocess.run([lean,*args],cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
 order=[];pending=set(mods);records={}
 while pending:
  ready=sorted(n for n in pending if not(set(mods[n]['imports'])&pending));assert ready,'Cyclic imports'
  for n in ready:
   obj=objects/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);source=ROOT/mods[n]['path'];log=out/'logs'/(n+'.compile.log')
   run(['--deps',str(source)],ROOT/'lean',out/'logs'/(n+'.deps.log'))
   run(['-o',str(obj),str(source)],ROOT/'lean',log);records[n]={'source_sha256':digest(source),'object_sha256':digest(obj),'compile_log_sha256':digest(log)};print('Compiled',n,flush=True)
  order+=ready;pending.difference_update(ready)
 for helper in ['FullTreeAuditSupportFast','ExactKernelTypes']:
  src=ROOT/'tools'/(helper+'.lean');run(['-o',str(out/'helpers'/(helper+'.olean')),str(src)],src.parent,out/'logs'/(helper+'.log'))
 driver=out/'Audit.lean';inv=out/'inventory.json';targets=', '.join(order)
 driver.write_text('\n'.join(['import FullTreeAuditSupportFast','import ExactKernelTypes',*('import '+n for n in order),'set_option pp.fullNames true','set_option pp.universes true','set_option pp.explicit true','set_option pp.notation false','set_option pp.deepTerms true','set_option pp.maxSteps 1000000','#verify_full_tree_inventory ['+targets+'] to '+json.dumps(str(inv)),*('#fast_full_tree_audit '+n+' to '+json.dumps(str(out/'audits'/(n+'.json'))) for n in order),'#exact_kernel_types ['+targets+'] to '+json.dumps(str(out/'exact_types'))])+'\n')
 run([str(driver)],out,out/'logs/audit.log');inventory=json.loads(inv.read_text());assert inventory['all_match'] and inventory['module_count']==563
 by={r['module']:r for r in inventory['modules']};allowed={'propext','Classical.choice','Quot.sound'};total=0;content=(out/'logs/audit.log').read_text()
 for n in order:
  d=json.loads((out/'audits'/(n+'.json')).read_text());rows=d['records'];assert d['environment_constant_count']==len(rows);names={r['name'] for r in rows}
  assert len(names)==len(rows) and set(by[n]['kernel_names'])==names
  assert all(r['module']==n and r['builtin_check_and_print_axioms_invoked'] and r['kind']!='axiom' and set(r['axioms'])<=allowed for r in rows)
  raw=json.loads((out/'exact_types'/(n+'.json')).read_text());assert raw['count']==len(rows) and {r['name'] for r in raw['records']}==names
  for r in rows:assert f"FULL_TREE_PAIR_BEGIN {r['name']}\n" in content and f"FULL_TREE_PAIR_END {r['name']}\n" in content
  records[n].update(audit_sha256=digest(out/'audits'/(n+'.json')),raw_types_sha256=digest(out/'exact_types'/(n+'.json')));total+=len(rows)
 for app in ['SharpApplicationInstantiations','SharpApplicationFullyApplied']:
  run([str(ROOT/'tools'/(app+'.lean'))],ROOT/'tools',out/'logs'/(app+'.log'))
 inputs();assert total==7970 and 'EXACT_KERNEL_TYPES_DONE 563 7970' in content
 result={'passed':True,'scope':'Fresh compilation of all563 sources followed by complete kernel audit in this new portable run','modules':563,'declarations':total,'allowed_axioms':sorted(allowed),'reused_project_objects':0,'exact_application_instantiations_passed':True,'records':records}
 (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: 563 fresh modules, 7970 audited declarations')
if __name__=='__main__':main()
