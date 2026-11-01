"""Reproduce five reviewed renderer/evidence boundary bugs in temporary fixtures."""
from pathlib import Path
import json, subprocess, tempfile, re
# Run after `cargo build --bins` in v2. All mutations and synthetic reviews
# are confined to a fresh temporary directory, never repository evidence.
BIN=Path(__file__).resolve().parents[2] / 'target/debug'
BASE=Path(tempfile.mkdtemp(prefix='dada-review-'))

def write(root,path,body):
 p=root/path; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(body)
def fixture(name,unit):
 root=BASE/name; root.mkdir()
 files={'spec.json':json.dumps({'schema':1,'chapters':['md/model.md'],'policies':['policy.md']}),'md/model.md':'# Model\n\n'+unit,'policy.md':'Synthetic fixture policy, no real review.\n','Cargo.toml':'[workspace]\n','Cargo.lock':'version = 4\n','mdbook-dada/Cargo.toml':'[package]\nname="fixture"\nversion="0.1.0"\n','mdbook-dada/src/lib.rs':'pub fn validate() {}\n','mdbook-dada/tests/basic.rs':'#[test]\nfn checked() {}\n','lean/Fixture.lean':'def value : Nat := 1\nabbrev Thing := Nat\n','lean/lean-toolchain':'leanprover/lean4:v4.35.0\n','lean/lakefile.toml':'name = "fixture"\n','lean/lake-manifest.json':'{"packages":[]}\n','book.toml':'[preprocessor.dada]\nlean-source = "lean"\n'}
 for path,body in files.items():write(root,path,body)
 return root

def cmd(root,*args):
 p=subprocess.run([str(BIN/'dada-spec'),*args],cwd=root,text=True,capture_output=True)
 if p.returncode:raise Exception(p.stdout+p.stderr)
 return p.stdout

def approve(root):
 path=Path(cmd(root,'prepare','model.value').splitlines()[0]); bundle=json.loads(path.read_text())
 review={'schema':1,'bundle':bundle['digest'],'reviewer':'synthetic adversarial fixture','provenance':'Temporary validator counterexample; no real review.','examined':[i['key'] for i in bundle['inputs'] if i['key'].split(':')[0] in ['unit','lean','rust','test','policy','extra']],'conclusion':'corresponds','rationale':'Synthetic fixture approval for validator test only.','limitations':['Does not establish any semantic claim.'],'supersedes':[]}
 write(root,'review.json',json.dumps(review));cmd(root,'record',str(path),str(root/'review.json'))
 return bundle

def render(root):
 context={'renderer':'html','root':str(root),'config':{'preprocessor':{'dada':{'lean-source': re.search(r'lean-source = "([^"]+)"', (root/'book.toml').read_text())[1]}}}}
 book={'sections':[{'Chapter':{'path':'model.md','content':(root/'md/model.md').read_text(),'sub_items':[]}}]}
 p=subprocess.run([str(BIN/'mdbook-dada')],input=json.dumps([context,book]),text=True,capture_output=True)
 if p.returncode:raise Exception(p.stderr)
 return json.loads(p.stdout)['sections'][0]['Chapter']['content']

root=fixture('configured-root','```{definition} model.value\n:lean: Fixture:value\n\nThe value is one.\n```\n')
bundle=approve(root);before=render(root)
write(root,'lean-alt/Fixture.lean','def value : Nat := 2\n');write(root,'book.toml','[preprocessor.dada]\nlean-source = "lean-alt"\n')
after=render(root)
print('configured-root:',cmd(root,'check').strip(),'render changed=',before!=after,'render includes 2=',':= 2' in after,'book config in bundle=',any(i['path']=='book.toml' for i in bundle['inputs']))
write(root,'before.html',before);write(root,'after.html',after)

root=fixture('nested-legacy','````{definition} model.value\n:rust: mdbook-dada/src/lib.rs:validate\n\nThe renderer displays this grammar.\n\n```{grammar} Fixture:Thing\nt ::= Nat\n```\n````\n')
bundle=approve(root);before=render(root)
write(root,'lean/Fixture.lean','def value : Nat := 1\nabbrev Thing := Bool\n');after=render(root)
print('nested-legacy:',cmd(root,'check').strip(),'render changed=',before!=after,'render includes Bool=', 'Bool' in after,'lean paths in bundle=',[i['path'] for i in bundle['inputs'] if i['path'].startswith('lean/')])
write(root,'before.html',before);write(root,'after.html',after)

root=fixture('truncated-rule','```{rule} model.value\n:lean: Fixture:Indexed.zero\n\nT\n```\n')
write(root,'lean/Fixture.lean','inductive Indexed : String → Type where\n  | zero : Indexed "zero"\n')
out=render(root);write(root,'rendered.html',out)
bundle_path=Path(cmd(root,'prepare','model.value').splitlines()[0]);bundle=json.loads(bundle_path.read_text());selected=[i['content'] for i in bundle['inputs'] if i['key'].startswith('lean:')][0]
print('truncated-rule selected:',repr(selected))
print('fixtures:',BASE)
root=fixture('wrong-constructor','```{rule} model.value\n:lean: Fixture:First.second\n\nFirst has a second rule.\n```\n')
write(root,'lean/Fixture.lean','inductive First where\n  | first\n  inductive Second where\n  | second\n')
out=render(root);write(root,'rendered.html',out)
bundle=approve(root);selected=[i['content'] for i in bundle['inputs'] if i['key'].startswith('lean:')][0]
print('wrong-constructor:',cmd(root,'check').strip(),'selected=',repr(selected))
root=fixture('mdbook-include','```{definition} model.value\n:lean: Fixture:value\n\n{{#include details.txt}}\n```\n')
write(root,'md/SUMMARY.md','# Summary\n\n[Model](model.md)\n')
write(root,'md/details.txt','The value is one.\n')
write(root,'book.toml','[book]\nsrc = "md"\ntitle = "Fixture"\n[preprocessor.dada]\ncommand = "'+str(BIN/'mdbook-dada')+'"\nafter = ["index"]\nlean-source = "lean"\n')
bundle=approve(root)
def build(root):
 p=subprocess.run(['mdbook','build'],cwd=root,text=True,capture_output=True)
 if p.returncode:raise Exception(p.stdout+p.stderr)
 return (root/'book/model.html').read_text()
before=build(root)
write(root,'md/details.txt','The value is two, not one.\n')
after=build(root)
print('mdbook-include:',cmd(root,'check').strip(),'render changed=',before!=after,'render contains changed prose=','The value is two, not one.' in after,'included file in bundle=',any(i['path']=='md/details.txt' for i in bundle['inputs']))
