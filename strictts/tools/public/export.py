"""Per-function result tables for tools/public/results/ (no source code, no IR):
coverage_<name>.tsv (one row per function and mode) and proofs.tsv (one row per proof attempt).

usage: python3 -I tools/public/export.py OUTDIR AUTODIR DEST NAME... -- LABEL=MODULE... [--nopanic FINAL.json]
  (--nopanic: append the rows of the uniform NoPanic sweep, tools/public/np_report.py)
"""
import json
import os
import sys


def main():
    argv = sys.argv[1:]
    nopanic = None
    if '--nopanic' in argv:
        i = argv.index('--nopanic'); nopanic = argv[i + 1]; del argv[i:i + 2]
    sep = argv.index('--')
    outdir, autodir, dest = argv[:3]
    names, mods = argv[3:sep], argv[sep + 1:]
    os.makedirs(dest, exist_ok=True)
    for name in names:
        lines = ['mode\tfile\tline\tname\tkind\tloc\tstatus\trules']
        for mode in ('strict', 'dyn', 'dynany'):
            p = os.path.join(outdir, f'{name}.{mode}.json')
            if not os.path.exists(p):
                continue
            for r in json.load(open(p))['rows']:
                rules = ','.join(f'{k}:{v}' for k, v in sorted(r['rules'].items()))
                lines.append(f"{mode}\t{r['file']}\t{r['line']}\t{r['name']}\t{r['kind']}\t{r['loc']}\t{r['status']}\t{rules}")
        open(os.path.join(dest, f'coverage_{name}.tsv'), 'w').write('\n'.join(lines) + '\n')
    lines = ['set\tfunction\tsource\targs\tret\tloops\tcallbacks\tuses_unknown\tverdict\tclass\tcounterexample']
    for spec in mods:
        label, _, mod = spec.partition('=')
        for r in json.load(open(os.path.join(autodir, f'{mod}_results.json'))):
            lines.append('\t'.join([label, r['fn'], r['source'], ' '.join(r['args']), r['ret'], ','.join(r['loops']),
                                    ','.join(r['callbacks']), str(bool(r.get('uses_dyn'))).lower(), r['verdict'], r['category'],
                                    r.get('counterexample', '')]))
    if nopanic:
        for e in json.load(open(nopanic)):
            verdict = e['verdict']
            cls = e.get('class') or (e.get('stuck') or ['', ''])[0]
            detail = e.get('input', '') if verdict == 'COUNTEREXAMPLE' else (e.get('stuck') or ['', ''])[1][:120]
            lines.append('\t'.join([f"uniform NoPanic: {e['set']}", e['fn'], e['source'], ' '.join(e['args']), e['ret'],
                                    ','.join(e['loops']), ','.join(e['callbacks']), str(bool(e['uses_dyn'])).lower(),
                                    verdict, cls, detail.replace('\t', ' ')]))
    open(os.path.join(dest, 'proofs.tsv'), 'w').write('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
