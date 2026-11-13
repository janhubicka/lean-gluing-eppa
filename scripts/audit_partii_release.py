#!/usr/bin/env python3
"""Read-only release evidence for the recursive valuation paper and Lean stack.

Compare identical compilation settings, keep source length separate from PDF
pages, verify frozen text, and identify PRs already present by Git ancestry.
No PR is merged/closed and no repository source is rewritten by this script.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'proof-audit' / 'release'
BASE = '1944cfc4bf5c72ef473963c7871d5115953432b7'
CANDIDATE = 'd815d5c1e0544a150ed918331c6c6f5dd19dd979'
CHECKED_LEAN = '3b9b5ac52b354d789844ec1f06b6cd50552f8889'
MASTER = 'steiner_recursive_gluing_valuations.tex'
TEX = [MASTER, 'part_ii_local_tree_realizations.tex',
       'part_ii_chain_valuations.tex', 'part_iii_steiner_applications.tex',
       'appendix_short_path_obstruction.tex']


def run(args, cwd=ROOT, check=True, timeout=600):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout)
    if check and p.returncode:
        raise RuntimeError('Command failed: ' + ' '.join(map(str, args)) + '\n' + p.stdout[-6000:])
    return p


def api(path):
    req = urllib.request.Request('https://api.github.com/repos/janhubicka/lean-gluing-eppa/' + path,
          headers={'Accept': 'application/vnd.github+json',
                   'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                   'User-Agent': 'part-ii-release-audit'})
    with urllib.request.urlopen(req, timeout=45) as r:
        return json.load(r)


def uncomment(s):
    return '\n'.join(re.split(r'(?<!\\)%', x, maxsplit=1)[0] for x in s.splitlines())


def expand(directory, name, ancestors=()):
    if name in ancestors:
        raise ValueError('Recursive input: ' + name)
    text = uncomment((directory / name).read_text())
    def sub(m):
        q = m[1] if m[1].endswith('.tex') else m[1] + '.tex'
        return '' if q == 'validation.tex' else expand(directory, q, ancestors + (name,))
    return re.sub(r'\\input\{([^}]+)\}', sub, text)


def source_summary(directory):
    text = expand(directory, MASTER)
    labels = re.findall(r'\\label\{([^}]+)\}', text)
    refs = re.findall(r'\\(?:eqref|ref|pageref|autoref|cref|Cref)\{([^}]+)\}', text)
    bib = re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}', text)
    cites = [x.strip() for a in re.findall(r'\\cite(?:\[[^\]]*\])*\{([^}]+)\}', text) for x in a.split(',')]
    stack, errors = [], []
    for kind, env in re.findall(r'\\(begin|end)\{([^}]+)\}', text):
        if kind == 'begin':
            stack.append(env)
        elif not stack or stack.pop() != env:
            errors.append(env)
    missing_markers = []
    for name in TEX[1:]:
        for match in re.finditer(r'\\begin\{(theorem|lemma|corollary)\}(.*?)\\end\{\1\}',
                                (directory / name).read_text(), re.S):
            statement = match[2]
            label = re.search(r'\\label\{([^}]+)\}', statement)
            if not re.search(r'\\lean(?:verified|partial|pending)', statement):
                missing_markers.append({'file': name, 'label': label[1] if label else None})
    return {'files': {p: {'lines': len((directory / p).read_text().splitlines()),
                          'characters': len((directory / p).read_text()),
                          'nonblank_lines': sum(bool(x.strip()) for x in (directory / p).read_text().splitlines())}
                       for p in TEX},
            'labels': labels, 'references': len(refs), 'citations': len(cites),
            'unresolved_refs': sorted(set(refs) - set(labels)),
            'unresolved_cites': sorted(set(cites) - set(bib)),
            'duplicate_labels': sorted({x for x in labels if labels.count(x) > 1}),
            'environment_errors': errors + stack,
            'missing_statement_markers': missing_markers,
            'pinned_green_markers': re.findall(r'\\leanverifiedpinned\{[^}]*\}\{[^}]*\}\{[^}]*\}', text)}


def manuscript(pdf=False):
    repo = OUT / 'paper-git'
    if not repo.exists():
        run(['git', 'clone', '--quiet', '--filter=blob:none', '--no-checkout',
             'https://github.com/janhubicka/Otto-simplified.git', str(repo)])
    report = {'baseline': BASE, 'candidate': CANDIDATE,
              'settings': 'same checked-in preamble, fonts, validation.tex and latexmk command'}
    work = {}
    for kind, sha in [('baseline', BASE), ('candidate', CANDIDATE)]:
        run(['git', 'fetch', '--quiet', 'origin', sha], cwd=repo)
        directory = OUT / (kind + '-source')
        if not directory.exists():
            run(['git', 'worktree', 'add', '--quiet', '--detach', str(directory), sha], cwd=repo)
        assert run(['git', 'rev-parse', 'HEAD'], cwd=directory).stdout.strip() == sha
        work[kind] = directory
        report[kind + '_source'] = source_summary(directory)
    first, second = work['baseline'], work['candidate']
    a, b = (first / MASTER).read_text(), (second / MASTER).read_text()
    anchor = "\\section{Comparison with Otto's constructions}"
    suffix = '\\input{appendix_short_path_obstruction.tex}'
    report['frozen_prefix_unchanged'] = a.split(anchor)[0] == b.split(anchor)[0]
    report['bibliography_suffix_unchanged'] = a[a.index(suffix):] == b[b.index(suffix):]
    report['validation_macros_unchanged'] = (first / 'validation.tex').read_bytes() == (second / 'validation.tex').read_bytes()
    report['old_green_markers_unchanged'] = report['baseline_source']['pinned_green_markers'] == report['candidate_source']['pinned_green_markers']
    report['lost_labels'] = sorted(set(report['baseline_source']['labels']) - set(report['candidate_source']['labels']))
    for k in ['frozen_prefix_unchanged', 'bibliography_suffix_unchanged', 'validation_macros_unchanged', 'old_green_markers_unchanged']:
        assert report[k], k
    for k in ['unresolved_refs', 'unresolved_cites', 'duplicate_labels', 'environment_errors']:
        assert not report['candidate_source'][k], (k, report['candidate_source'][k])
    assert not report['lost_labels']
    for script in ['validation/local-tree/check_referee_20261113.py',
                   'validation/local-tree/apply_referee_20261113.py']:
        cmd = ['python3', script] + (['--check'] if 'apply_' in script else [])
        result = run(cmd, cwd=second, check=False)
        (OUT / (Path(script).stem + '.log')).write_text(result.stdout)
        report[Path(script).stem] = {'returncode': result.returncode, 'tail': result.stdout[-2500:]}
    for kind, directory in work.items():
        if pdf:
            texcount = run(['texcount', '-inc', '-sum', '-1', MASTER], cwd=directory, check=False)
            (OUT / (kind + '-texcount.log')).write_text(texcount.stdout)
            counts = re.findall(r'^\s*(\d+)\s*$', texcount.stdout, re.M)
            report[kind + '_texcount'] = int(counts[-1]) if texcount.returncode == 0 and counts else None
            build = OUT / (kind + '-build')
            build.mkdir(exist_ok=True)
            result = run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                          '-file-line-error', '-outdir=' + str(build), MASTER], cwd=directory,
                         check=False, timeout=900)
            (OUT / (kind + '-latex.log')).write_text(result.stdout)
            pdfpath = build / MASTER.replace('.tex', '.pdf')
            report[kind + '_build_returncode'] = result.returncode
            if result.returncode == 0 and pdfpath.exists():
                info = run(['pdfinfo', str(pdfpath)]).stdout
                (OUT / (kind + '-pdfinfo.log')).write_text(info)
                report[kind + '_pages'] = int(re.search(r'^Pages:\s+(\d+)', info, re.M)[1])
                run(['pdftotext', str(pdfpath), str(OUT / (kind + '-pdf-text.txt'))])
                pdftext = (OUT / (kind + '-pdf-text.txt')).read_text()
                report[kind + '_pdf_words'] = len(re.findall(r'\S+', pdftext))
            else:
                report[kind + '_build_failure'] = result.stdout[-6000:]
    report['source_line_delta'] = sum(v['lines'] for v in report['candidate_source']['files'].values()) - sum(v['lines'] for v in report['baseline_source']['files'].values())
    report['source_character_delta'] = sum(v['characters'] for v in report['candidate_source']['files'].values()) - sum(v['characters'] for v in report['baseline_source']['files'].values())
    if 'candidate_pages' in report and 'baseline_pages' in report:
        report['page_delta'] = report['candidate_pages'] - report['baseline_pages']
    (OUT / ('manuscript-pdf.json' if pdf else 'manuscript-source.json')).write_text(json.dumps(report, indent=2))
    print(json.dumps({k: v for k, v in report.items() if not k.endswith('_source')}, indent=2), flush=True)
    print('MISSING MARKERS:', json.dumps(report['candidate_source']['missing_statement_markers']), flush=True)


def pr_inventory():
    run(['git', 'fetch', '--quiet', '--no-tags', 'origin', '+refs/heads/*:refs/remotes/origin/*'])
    pulls = []
    page = 1
    while True:
        batch = api(f'pulls?state=open&per_page=100&page={page}')
        pulls.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    def inspect(p):
        sha = p['head']['sha']
        ancestor = run(['git', 'merge-base', '--is-ancestor', sha, CHECKED_LEAN], check=False).returncode == 0
        runs = api('actions/runs?head_sha=' + sha + '&per_page=30')['workflow_runs']
        latest = {}
        for r in runs:
            latest.setdefault(r['name'], {'id': r['id'], 'status': r['status'], 'conclusion': r['conclusion']})
        return {'pr': p['number'], 'head': sha, 'head_branch': p['head']['ref'],
                'base_branch': p['base']['ref'], 'draft': p['draft'],
                'ancestor_of_checked_163': ancestor, 'latest_runs': latest,
                'title': p['title']}
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        records = list(pool.map(inspect, pulls))
    (OUT / 'pull-inventory.json').write_text(json.dumps(records, indent=2))
    for r in records:
        print('PR', r['pr'], 'ANCESTOR', r['ancestor_of_checked_163'],
              'BASE', r['base_branch'], 'HEAD', r['head'],
              'CI', json.dumps(r['latest_runs']), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--pdf', action='store_true')
    p.add_argument('--inventory', action='store_true')
    args = p.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    if args.inventory:
        pr_inventory()
    else:
        manuscript(args.pdf)


if __name__ == '__main__':
    main()
