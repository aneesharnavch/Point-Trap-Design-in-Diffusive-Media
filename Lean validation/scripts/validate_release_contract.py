#!/usr/bin/env python3
"""Exercise release evidence checks, including metadata-corruption rejection.

These checks test the release/audit contract, not mathematical propositions.
All corruption fixtures are temporary copies of metadata; source files and
historical certificates are never modified.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import tempfile
import sys
sys.dont_write_bytecode = True
from release_verify import source_check, theorem_names


def fixture(bundle, mutate):
    with tempfile.TemporaryDirectory(prefix='contract-', dir=bundle/'validation') as raw:
        root=Path(raw)
        for p in bundle.iterdir():
            if p.name not in ['manifest.json','validation']:
                (root/p.name).symlink_to(p.resolve(), target_is_directory=p.is_dir())
        (root/'validation').symlink_to((bundle/'validation').resolve(),target_is_directory=True)
        data=json.loads((bundle/'manifest.json').read_text())
        mutate(root,data)
        (root/'manifest.json').write_text(json.dumps(data))
        try:
            source_check(root)
        except ValueError as error:
            return str(error)
        raise AssertionError('Corrupt release metadata was accepted')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    base=Path(__file__).resolve().parent.parent
    ap.add_argument('--bundle',type=Path,default=base if (base/'manifest.json').exists() else base/'source-bundle')
    args=ap.parse_args();bundle=args.bundle.resolve();manifest,modules=source_check(bundle)
    scripts=Path(__file__).resolve().parent
    for name in ['release_verify.py','validate_examples.py','validate_release_contract.py']:
        ast.parse((scripts/name).read_text(),filename=name)
    def wrong_count(root,data):data['research_module_count']+=1
    def wrong_binding(root,data):
        row=next(r for r in data['files'] if r.get('original_path')=='TimeTraps.lean')
        row['original_path']='TimeTraps/nonexistent.lean'
    def missing_source_record(root,data):
        data['files']=[r for r in data['files'] if r.get('original_path')!='TimeTraps.lean']
    def wrong_index(root,data):
        p=root/'theorem-index.json';index=json.loads(p.read_text());p.unlink()
        index[0]['name']='TimeTraps.WrongNamespace.'+index[0]['name'].rsplit('.',1)[-1]
        p.write_text(json.dumps(index))
        row=next(r for r in data['files'] if r['bundle_path']=='theorem-index.json')
        row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
    results={'kind':'publication metadata checks; not Lean theorem verification',
      'uncorrupted_release_passed':True,'python_syntax_passed':True,
      'incorrect_count_rejected':fixture(bundle,wrong_count),
      'unbound_source_provenance_rejected':fixture(bundle,wrong_binding),
      'omitted_source_hash_record_rejected':fixture(bundle,missing_source_record),
      'wrong_namespace_index_rejected':fixture(bundle,wrong_index),
      'successive_namespace_modules':[p.relative_to(bundle/'lean').as_posix()
        for p in modules if p.read_text().count('\nnamespace ')>1],
      'fresh_clean_lean_build_performed':False}
    assert len(results['successive_namespace_modules'])==5
    target=bundle/'validation/release-contract.json';target.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
