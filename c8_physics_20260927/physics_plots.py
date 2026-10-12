#!/usr/bin/env python3
"""Two publication figures from the already checked physics dataset.

ROOT alone executes, through hi_cft_safe_run.py --limit-mib 1024.
Expected peak <256 MiB, requested AS1 GiB, runtime <20 seconds.
Only a few thousand CSV rows and two small vector figures are resident;
there is no mode engine, spectral recomputation, interpolation, or fit.
PDF and SVG output; exact inputs and their producer summary are hashed.
"""

import argparse
import csv
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from math import log10
import os
from pathlib import Path
import resource
import tempfile
from time import monotonic


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536),b''):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    need(path.stat().st_size <= 10*1024**2,'JSON input exceeds10MiB review cap')
    return json.loads(path.read_text(encoding='utf-8'))


def read_tsv(path):
    need(path.stat().st_size <= 10*1024**2,'TSV input exceeds10MiB review cap')
    with path.open(encoding='utf-8',newline='') as stream:
        rows = list(csv.DictReader(stream,delimiter='\t'))
    need(len(rows) <= 50000,'too many rows for this fixed-cutoff figure')
    return rows


def frac_label(x):
    x = Fraction(x)
    if x.denominator == 1:
        return f'${x.numerator}$'
    return f'${x.numerator}/{x.denominator}$'


def save(fig, output, stem, plt):
    # Vector backends preserve publication quality; no raster image arrays.
    fig.savefig(output/(stem+'.pdf'),bbox_inches='tight',metadata={
        'Title':stem.replace('_',' '),'Creator':'physics_plots.py; checked c8 dataset'})
    fig.savefig(output/(stem+'.svg'),bbox_inches='tight',metadata={
        'Title':stem.replace('_',' '),'Creator':'physics_plots.py; checked c8 dataset'})
    plt.close(fig)


def primary_figure(rows, scalars, output, plt):
    points = [(Fraction(r['Delta']),int(r['spin']),int(r['Virasoro_primaries']))
              for r in rows if 0 < Fraction(r['Delta']) <= 6 and int(r['Virasoro_primaries']) > 0]
    light = [(Fraction(r['Delta']),int(r['Virasoro_primaries']))
             for r in scalars if r['theory'] == 'diagonal_U' and 0 < Fraction(r['Delta']) < 2]
    need(light == [(Fraction(2,3),9),(Fraction(10,13),25),(Fraction(12,13),49),
                   (Fraction(14,13),169),(Fraction(16,13),196),(Fraction(4,3),729),
                   (Fraction(22,13),1764)],'relevant scalar control')
    need(all(d >= abs(s) for d,s,m in points),'unitarity cone')
    need(sum(m for d,m in light) == 2941,'relevant scalar total')
    logs = [log10(m) for d,s,m in points]
    fig,(left,right) = plt.subplots(1,2,figsize=(10.5,4.65),
                                   gridspec_kw={'width_ratios':[1.55,1]},constrained_layout=True)
    left.axhspan(0,2,color='#f3f3f3',zorder=0)
    left.axhline(2,color='#8c8c8c',linewidth=.75,linestyle='--',zorder=1)
    left.plot([-6,0,6],[6,0,6],color='#b5b5b5',linewidth=.7,linestyle=':',zorder=1)
    dots = left.scatter([s for d,s,m in points],[float(d) for d,s,m in points],
                        s=[12+10*v for v in logs],c=logs,cmap='viridis',
                        edgecolors='none',alpha=.88,zorder=3)
    left.set(xlim=(-6.6,6.6),ylim=(0,6.18),xticks=range(-6,7,2),yticks=range(7),
             xlabel=r'Spin $s=h-\bar h$',ylabel=r'Scaling dimension $\Delta=h+\bar h$',
             title=r'(a) Diagonal $U$: all Virasoro primaries, $0<\Delta\leq6$')
    left.grid(axis='y',alpha=.18,linewidth=.6)
    colorbar = fig.colorbar(dots,ax=left,shrink=.85,pad=.02)
    colorbar.set_label(r'$\log_{10}$ multiplicity',fontsize=9)
    left.text(.025,.035,'Shaded: relevant operators',transform=left.transAxes,fontsize=8,
              color='#555555',va='bottom')
    ypos = list(range(len(light)))
    right.barh(ypos,[m for d,m in light],height=.66,color='#286c9a')
    right.set(xscale='log',xlim=(1,4000),yticks=ypos,
              yticklabels=[frac_label(d) for d,m in light],xlabel='Primary components (log scale)',
              ylabel=r'Scalar dimension $\Delta$',title='(b) Relevant scalar multiplicities')
    right.invert_yaxis()
    right.grid(axis='x',which='major',alpha=.18,linewidth=.6)
    for i,(d,m) in enumerate(light):
        right.annotate(str(m),(m,i),xytext=(4,0),textcoords='offset points',
                       va='center',ha='left',fontsize=9)
    right.text(.98,.99,'2941 components in total',transform=right.transAxes,
               fontsize=8,va='top',ha='right')
    save(fig,output,'physics_primary_spectrum',plt)
    return {'Delta_cutoff_inclusive':'6','identity_included':False,
            'plotted_Delta_spin_pairs':len(points),
            'marker_area_in_points_squared':'12+10*log10(multiplicity)',
            'color':'log10(multiplicity)','relevant_scalar_components':2941,
            'scope':'Individual Virasoro-primary components, aggregated by exact Delta and integer spin; not merely extended-sector ground states.'}


def thermal_figure(rows, output, plt):
    theories = {'diagonal_U':{'label':r'Diagonal $U$','color':'#286c9a','marker':'o'},
                'E8_full':{'label':r'Full $E_8$','color':'#b84e39','marker':'s'}}
    expected = [Fraction(1,2),Fraction(3,4),Fraction(1),Fraction(3,2),Fraction(2)]
    fig,axes = plt.subplots(1,2,figsize=(9.3,3.9),constrained_layout=True)
    maximum_widths = {}
    for ax,key,title,ylabel in zip(axes,('heat_capacity','entropy'),
                                  ('(a) Heat capacity','(b) Thermal entropy'),
                                  (r'$C_V$',r'$S$')):
        maximum_widths[key] = Decimal(0)
        for name,style in theories.items():
            chosen = sorted((r for r in rows if r['theory'] == name),key=lambda r:Fraction(r['t']))
            need([Fraction(r['t']) for r in chosen] == expected,'five saved temperatures required')
            mids,errors = [],[]
            for row in chosen:
                lo,hi = Decimal(row[key+'_lower']),Decimal(row[key+'_upper'])
                need(0 < lo <= hi,'positive certified thermal interval')
                with localcontext() as ctx:
                    ctx.prec = 100
                    midpoint = (lo+hi)/2
                    radius = (hi-lo)/2
                    maximum_widths[key] = max(maximum_widths[key],hi-lo)
                mids.append(float(midpoint))
                errors.append(float(radius))
            ax.errorbar([float(t) for t in expected],mids,yerr=errors,
                        linestyle='none',marker=style['marker'],markersize=6,
                        markerfacecolor=style['color'] if name == 'diagonal_U' else 'none',
                        markeredgewidth=1.15,color=style['color'],capsize=2,elinewidth=.8,
                        label=style['label'],zorder=3)
        ax.set(xlim=(.4,2.1),xticks=[float(t) for t in expected],
               xticklabels=[frac_label(t) for t in expected],yscale='log',
               xlabel=r'$t=\beta v/L$',ylabel=ylabel,title=title)
        ax.grid(axis='both',which='major',alpha=.2,linewidth=.6)
        ax.axvline(1,color='#b5b5b5',linewidth=.7,linestyle=':',zorder=1)
    axes[0].legend(frameon=False,fontsize=9,loc='lower left')
    save(fig,output,'physics_thermal_comparison',plt)
    return {'temperatures_beta_v_over_L':[str(t) for t in expected],
            'observables':['heat_capacity','entropy'],
            'maximum_input_interval_width':{k:str(v) for k,v in maximum_widths.items()},
            'lines_between_data_points':False,
            'scope':'Only the five saved temperatures are plotted. Error bars are the conditional certified input intervals and are smaller than the markers. Floating-point conversion is for plotting only.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=Path(__file__).resolve().parent/'data')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'figures')
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    need(0 < cap <= 1024**3,'run under the permanent launcher with --limit-mib1024 or lower')
    started = monotonic()
    data,output = args.data.resolve(),args.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    artifact_names = [stem+suffix for stem in ('physics_primary_spectrum','physics_thermal_comparison')
                      for suffix in ('.pdf','.svg')]+['physics_plots.json']
    need(not any((output/name).exists() for name in artifact_names),'refusing to overwrite plot output')
    summary_path = data/'run_summary.json'
    summary = read_json(summary_path)
    need(summary['status'] == 'PASS' and summary['complete_full_CFT_Delta_max'] >= 6,
         'passed and complete spectral input required')
    need(summary['checks']['thermal_interval_consistency'] is True,'checked thermal intervals required')
    source_paths = [data/name for name in ('diagonal_spectrum.tsv','scalars.tsv','thermal.tsv')]
    for source in source_paths:
        need(summary['output_sha256'][source.name] == sha(source),'input differs from checked producer report')
    spectrum,scalars,thermal = [read_tsv(path) for path in source_paths]
    # Keep Matplotlib's font cache local and temporary; never touch a user's
    # global plotting configuration. No TeX or external subprocess is used.
    with tempfile.TemporaryDirectory(prefix='c8-physics-mpl-') as config:
        os.environ['MPLCONFIGDIR'] = config
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
                             'axes.titlesize':10,'axes.spines.top':False,'axes.spines.right':False,
                             'axes.axisbelow':True,'pdf.fonttype':42,'svg.fonttype':'none',
                             'savefig.dpi':180,'text.usetex':False})
        primary = primary_figure(spectrum,scalars,output,plt)
        thermal_record = thermal_figure(thermal,output,plt)
        version = matplotlib.__version__
    report = {'status':'PASS','schema':'haagerup-c8-physics-plots-v1','primary_figure':primary,
              'thermal_figure':thermal_record,'matplotlib_version':version,
              'source_sha256':{str(p):sha(p) for p in source_paths+[summary_path,Path(__file__).resolve()]},
              'output_sha256':{name:sha(output/name) for name in artifact_names if name != 'physics_plots.json'},
              'elapsed_seconds':monotonic()-started,
              'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'scope':'Visualization of authenticated existing data only. No new coefficient computation, regression, interpolation, or bootstrap bound.'}
    with (output/'physics_plots.json').open('x',encoding='utf-8') as stream:
        json.dump(report,stream,indent=2)
        stream.write('\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
