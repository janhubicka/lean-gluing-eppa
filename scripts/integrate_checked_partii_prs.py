#!/usr/bin/env python3
"""Prepare integration of checked Part II branches, never write main.

Only the literal allowlisted heads with a successful full Lean run are
eligible. Resolve conflicts only in import aggregators and named axiom
manifests by retaining both sets of declarations. Never choose a side for
a conflicting proof file. The resulting branch still requires a full build.
"""
from __future__ import annotations
import json
import os
import re
import subprocess
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRANCH = 'partii-postmerge-validation-20261113'
HEADS = {
  145:'b54424990fed436bc726bebe976a30c6b4aae246',
  142:'f0e8679fb62cda68d85647022b02e611a86e582b',
  138:'5042f7b46988a25df2d430d3e53bad6f1a2ea016',
  118:'d7778c650ed7738b48c1d189ff03715b43ca23a8',
  115:'78996752d25f7d16ebcb260740ca24c68e0f0027',
  106:'01f41e60f63d8dd4382995729c8dc512f011534b',
  104:'fbdc17a26ca20f38808eda03cafd13cf5812876e',
  98:'9dee1a8c6675ba975150619684bf59263a5c5965',
  93:'851b340f70913f81c9f82a95a9ca83aef30447e3',
  91:'210bb28098f2c14d8eb4f71ee6930e2683ed3281',
  88:'e7507ef59d8e411e55a181fe1e76b63465889300',
  82:'2d87134b7bf1ccd7909c4b07ad96f3f4658379d0',
  123:'9323526b1e8a2b2b12ce4adde68a52af3748404c',
  117:'8b48af7ce4f4370605545ecc99fc4f01fb63c11c',
  114:'a27f939648a4a72c04dcdf178352d14024345195',
  113:'0d373d01a2d94b9ec6b2caff1ae40c56d7c41f84',
  109:'f60415b9ae8181ed4907aa8f5dd8a7aab2c30458',
  105:'398eff7008f2fefb36384ae104484f62678c502f',
  97:'9843bfe87868f5ca8e4e8af29f5e238efe1e16e5',
  96:'be7bf28c624d97e410472acfd85dde1310e18245',
  92:'dc5a0f48dd08c3587d473c938b406cf98fcee9c8',
  86:'382df3d72e36e286ca702d3067a34aa717af29db',
  84:'bba38c6407184a4fb7649c99a96b90e3a837ad39',
  83:'72de4ae2b4369a110f98c7955d40476fef39a0e2',
  81:'8dfc9a54fffd206b4b2e328ba9c0e27be57bf9d5',
  65:'f6075c69040e607f5278fcc3b72cf8ca87c373dd',
  161:'0f36d38bd87338a05ecdab5c0dced327123a4120'
}


def git(*args, check=True):
    p = subprocess.run(['git', *args], cwd=ROOT, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if check and p.returncode:
        raise RuntimeError('git ' + ' '.join(args) + '\n' + p.stdout[-4000:])
    return p


def api(path):
    req = urllib.request.Request('https://api.github.com/repos/janhubicka/lean-gluing-eppa/' + path,
          headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],
                   'Accept':'application/vnd.github+json','User-Agent':'part-ii-integration'})
    with urllib.request.urlopen(req, timeout=45) as r:
        return json.load(r)


def merge_list_file(path):
    if not (path == 'GluingEPPA.lean' or path.endswith('/All.lean') or
            (path.startswith('scripts/Check') and path.endswith('Axioms.lean'))):
        return False
    a, b = git('show', ':2:'+path, check=False), git('show', ':3:'+path, check=False)
    if a.returncode or b.returncode:
        return False
    # Reject any executable declaration hidden inside an alleged aggregator.
    def stripped(s):
        s = re.sub(r'/\-.*?\-/', '', s, flags=re.S)
        s = re.sub(r'--[^\n]*', '', s)
        return s
    allowed = r'(?:import\s+[\w.]+|#print\s+axioms\s+[\w.]+)'
    for content in (a.stdout, b.stdout):
        if any(line.strip() and not re.fullmatch(allowed,line.strip()) for line in stripped(content).splitlines()):
            return False
    imports = list(dict.fromkeys(re.findall(r'^import\s+[\w.]+\s*$', a.stdout+'\n'+b.stdout, re.M)))
    axioms = list(dict.fromkeys(re.findall(r'^#print\s+axioms\s+[\w.]+\s*$', a.stdout+'\n'+b.stdout, re.M)))
    comments = '\n'.join(re.findall(r'/\-.*?\-/', a.stdout, re.S))
    (ROOT/path).write_text('\n'.join(s.strip() for s in imports)+'\n\n'+
                           ('\n'.join(s.strip() for s in axioms)+'\n\n' if axioms else '')+
                           comments+'\n')
    git('add','--',path)
    return True


def prune_redundant_root_imports():
    paths = {'GluingEPPA':ROOT/'GluingEPPA.lean'}
    paths.update({'GluingEPPA.'+'.'.join(p.relative_to(ROOT/'GluingEPPA').with_suffix('').parts):p
                  for p in (ROOT/'GluingEPPA').rglob('*.lean')})
    graph = {m:re.findall(r'^import\s+(GluingEPPA[\w.]*)\s*$', p.read_text(),re.M)
             for m,p in paths.items()}
    def reaches(start,target):
        seen, stack = set(), list(graph.get(start,[]))
        while stack:
            m = stack.pop()
            if m == target:
                return True
            if m not in seen:
                seen.add(m)
                stack.extend(graph.get(m,[]))
        return False
    direct = graph['GluingEPPA']
    redundant = {x for x in direct if any(y != x and reaches(y,x) for y in direct)}
    path = paths['GluingEPPA']
    lines = path.read_text().splitlines(True)
    path.write_text(''.join(l for l in lines if not (l.strip().startswith('import ') and l.strip()[7:] in redundant)))
    return sorted(redundant)


def main():
    assert os.environ.get('GITHUB_REF_NAME') == BRANCH
    assert git('branch','--show-current').stdout.strip() == BRANCH
    git('config','user.name','github-actions[bot]')
    git('config','user.email','41898282+github-actions[bot]@users.noreply.github.com')
    git('fetch','--quiet','--no-tags','origin','+refs/heads/*:refs/remotes/origin/*')
    records = []
    for number, sha in HEADS.items():
        p = api(f'pulls/{number}')
        if p['state'] != 'open' or p['head']['sha'] != sha:
            records.append({'pr':number,'status':'skip-closed-or-head-moved'})
            continue
        if git('merge-base','--is-ancestor',sha,'HEAD',check=False).returncode == 0:
            records.append({'pr':number,'status':'already-in-integration'})
            continue
        runs = api(f'actions/runs?head_sha={sha}&per_page=30')['workflow_runs']
        full = next((r for r in runs if r['name']=='Lean'), None)
        if not full or full['status'] != 'completed' or full['conclusion'] != 'success':
            records.append({'pr':number,'status':'skip-no-successful-exact-head'})
            continue
        attempt = git('merge','--no-ff','--no-commit',sha,check=False)
        conflicts = git('diff','--name-only','--diff-filter=U').stdout.splitlines()
        rejected = [path for path in conflicts if not merge_list_file(path)]
        if rejected or (attempt.returncode and not conflicts):
            git('merge','--abort',check=False)
            records.append({'pr':number,'status':'requires-manual-reconciliation','files':rejected,'head':sha})
            continue
        git('commit','-m',f'Integrate checked Part II PR #{number} ({sha[:12]}); full combined validation pending')
        records.append({'pr':number,'status':'integrated-pending-combined-build','head':sha,
                        'resolved_lists':conflicts,'prior_run':full['id']})
    pruned = prune_redundant_root_imports()
    if git('diff','--name-only').stdout.strip():
        git('add','GluingEPPA.lean')
        git('commit','-m','Remove redundant root imports after preserving all proof modules')
    out = ROOT/'validation/part-ii-checked-pr-integration-20261113.json'
    out.write_text(json.dumps({'status':'COMBINED_BUILD_REQUIRED','records':records,
                              'redundant_root_imports_removed':pruned},indent=2)+'\n')
    git('add',str(out.relative_to(ROOT)))
    git('commit','-m','Record checked-head integration decisions and unresolved proof conflicts')
    git('diff','--check')
    # A normal fast-forward push refuses any concurrent edits; never force.
    git('push','origin','HEAD:refs/heads/'+BRANCH)
    print(json.dumps({'source_sha':git('rev-parse','HEAD').stdout.strip(),
                      'records':records,'root_imports_removed':pruned},indent=2),flush=True)


if __name__ == '__main__':
    main()
