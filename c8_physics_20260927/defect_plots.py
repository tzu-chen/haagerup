#!/usr/bin/env python3
"""Publication plots from the checked fixed-rank defect dataset.

Run with hi_cft_safe_run.py; estimated <250 MiB, AS1GiB, no parallelism.
No published bound is interpolated or invented. bootstrap_model_points.pdf
contains only exact CFT points and the marginality threshold, not a curve.
"""
import argparse
import cmath
import csv
from fractions import Fraction
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap, BoundaryNorm


def exact_real(coefficients):
    if len(coefficients) != 12:
        raise ValueError('expected degree12 field encoding')
    root = cmath.exp(2j * cmath.pi / 13)
    value = sum(float(Fraction(q)) * root**j for j, q in enumerate(coefficients))
    if abs(value.imag) > 1e-8:
        raise ValueError('unexpected complex plotting datum')
    return value.real


def save(fig, output, name):
    fig.savefig(output/f'{name}.pdf', bbox_inches='tight')
    fig.savefig(output/f'{name}.svg', bbox_inches='tight')
    plt.close(fig)


def main(directory):
    source = directory/'defect_data.json'
    if source.stat().st_size > 20*1024*1024:
        raise ValueError('unexpectedly large input')
    data = json.loads(source.read_text())
    if data.get('schema') != 'haagerup-c8-defects-v1' or not all(data['checks'].values()):
        raise ValueError('checked dataset required')
    if len(data['labels']) != 12 or len(data['E8_H3']['U_preserving_boundary_annuli']) != 36:
        raise ValueError('run the complete fixed-rank exporter first')
    figures = directory/'figures'
    figures.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'savefig.dpi': 200, 'pdf.fonttype': 42, 'svg.fonttype': 'none'})
    labels = [r'$0$', r'$b$', r'$a$', r'$c_0$', r'$c_1$', r'$c_2$'] + [rf'$d_{j}$' for j in range(1,7)]
    h3labels = [r'$1$', r'$\alpha$', r'$\alpha^2$', r'$\rho$', r'$\alpha\rho$', r'$\alpha^2\rho$']
    xpos = np.arange(12)
    blue, red, gray = '#226A9A', '#B84C38', '#666666'
    dims = [exact_real(x) for x in data['dimensions_exact']]
    gU = [max(0, exact_real(x))**0.5 for x in data['Cardy_boundary_g_squared_exact']]
    gE8 = [exact_real(x) for x in data['E8_H3']['U_preserving_boundary_g_exact']]
    fig, axes = plt.subplots(2, 2, figsize=(11.2, 7.4), constrained_layout=True)
    ax = axes[0,0]
    ax.bar(xpos, dims, color=blue, width=.7)
    ax.set(xticks=xpos, xticklabels=labels, ylabel='Quantum dimension', title='(a) Twelve center lines')
    ax.grid(axis='y', alpha=.2)
    ax = axes[0,1]
    ax.scatter(xpos, gU, color=blue, marker='o', label='Diagonal U: Cardy boundaries')
    ax.scatter(np.arange(6)+13, gE8, color=red, marker='s', label=r'$E_8$: U-preserving boundaries')
    ax.axvline(12, color='#cccccc', linewidth=.8)
    ax.set(xticks=list(xpos)+list(np.arange(6)+13), xticklabels=labels+h3labels,
           ylabel=r'Boundary overlap $g$', title='(b) Boundary vacuum overlaps')
    ax.tick_params(axis='x', labelsize=7)
    ax.legend(frameon=False, fontsize=8, loc='upper left')
    ax.grid(axis='y', alpha=.2)
    ax = axes[1,0]
    twist = data['diagonal_U_twisted_sectors']
    grounds = [float(Fraction(x['ground_dimension'])) for x in twist]
    scalars = [float(Fraction(x['first_nonidentity_scalar_dimension'])) for x in twist]
    ax.plot(xpos, grounds, 'o-', color=blue, linewidth=1, label='Ground state (any spin)')
    ax.scatter(xpos, scalars, marker='D', facecolors='none', edgecolors=red,
               s=38, label='First nonidentity scalar', zorder=3)
    ax.set(xticks=xpos, xticklabels=labels, ylabel=r'Scaling dimension $\Delta$',
           title='(c) Diagonal U with a spatial defect', ylim=(-.03,.76))
    ax.set_yticks([0, 1/3, 2/3], ['0', r'$1/3$', r'$2/3$'])
    ax.legend(frameon=False, fontsize=8, loc='lower right')
    ax.grid(axis='y', alpha=.2)
    ax = axes[1,1]
    branching = np.asarray(data['E8_H3']['forgetful_n_x_mu'], dtype=int)
    cmap = ListedColormap(['#ffffff', '#BBD8E9', '#367BA1'])
    ax.imshow(branching, cmap=cmap, norm=BoundaryNorm([-.5,.5,1.5,2.5],3), aspect='auto')
    for x in range(6):
        for mu in range(12):
            if branching[x,mu]:
                ax.text(mu,x,str(branching[x,mu]),ha='center',va='center',fontsize=8,
                        color='white' if branching[x,mu]==2 else '#18374B')
    ax.set(xticks=xpos, xticklabels=labels, yticks=range(6), yticklabels=h3labels,
           title=r'(d) $n_{x\mu}$: Haagerup defect-sector multiplicities')
    save(fig, figures, 'defect_observables')

    rows = data['E8_H3']['U_preserving_boundary_annuli']
    index = {name: i for i,name in enumerate(data['E8_H3']['labels'])}
    gap = np.zeros((6,6))
    mult = np.zeros((6,6),dtype=int)
    for row in rows:
        x,y=index[row['x']],index[row['y']]
        gap[x,y]=float(Fraction(row['first_nonidentity_h']))
        mult[x,y]=row['multiplicity']
    fig,axes=plt.subplots(1,2,figsize=(8.4,3.8),constrained_layout=True)
    for ax, values, title in zip(axes,[gap,mult],[r'First positive boundary weight $h$', 'Multiplicity at that weight']):
        if values is gap:
            ax.imshow(values,cmap='Blues',vmin=0,vmax=1)
        else:
            ax.imshow(np.log10(values),cmap='Blues',vmin=0,vmax=np.log10(248))
        for x in range(6):
            for y in range(6):
                text=('1' if gap[x,y]==1 else '1/3') if values is gap else str(mult[x,y])
                ax.text(y,x,text,ha='center',va='center',color='white' if values[x,y] == values.max() else '#18374B')
        ax.set(xticks=range(6),xticklabels=h3labels,yticks=range(6),yticklabels=h3labels,title=title)
    fig.suptitle(r'$E_8$ theory: 36 annuli between U-preserving boundaries')
    save(fig,figures,'E8_boundary_annuli')

    points = [
      {'theory':'Diagonal U', 'sector':'all scalars', 'Delta':'2/3', 'comparison':'ordinary scalar bootstrap'},
      {'theory':'Full E8', 'sector':'all scalars', 'Delta':'2', 'comparison':'ordinary scalar bootstrap'},
      {'theory':'Diagonal U', 'sector':'all center Verlinde lines invariant', 'Delta':'2', 'comparison':'distinct center symmetry'},
      {'theory':'Full E8', 'sector':'left H3 invariant (V1)', 'Delta':'2', 'comparison':'AHKZ Figure2'},
      {'theory':'Full E8', 'sector':'Vpi2 union Vsigma1', 'Delta':'2', 'comparison':'AHKZ Figure3'},
    ]
    (figures/'bootstrap_model_points.json').write_text(json.dumps({'c_left':8,'c_right':8,'points':points,
       'curve_status':'No numerical exclusion curve is generated; these are exact model points.',
       'source_figures':'https://arxiv.org/html/2512.08225v2'},indent=2)+'\n')
    fig,ax=plt.subplots(figsize=(8.3,3.7),constrained_layout=True)
    descriptions=['Diagonal U: all scalars',r'Full $E_8$: all scalars',
                  r'Diagonal U: $Z(\mathcal{H}_3)$-invariant',
                  r'Full $E_8$: left $\mathcal{H}_3$-invariant',
                  r'Full $E_8$: $\mathcal{V}_{\pi_2}\cup\mathcal{V}_{\sigma_1}$']
    for j,p in enumerate(points):
        value=float(Fraction(p['Delta']))
        ax.scatter(value,4-j,s=52,color=blue if j<3 else red,marker='o' if j<3 else 'D',zorder=3)
        ax.text(value+.07,4-j,p['Delta'],va='center',fontsize=9)
    ax.axvline(2,linestyle='--',color=gray,linewidth=.8,label=r'Marginality: $\Delta=2$')
    ax.set(yticks=range(5),yticklabels=descriptions[::-1],xlim=(0,2.35),ylim=(-.6,4.6),
           xlabel=r'First nonidentity scalar dimension $\Delta$',title=r'Exact comparison points at $c_L=c_R=8$')
    ax.legend(frameon=False,loc='lower left',fontsize=8)
    ax.grid(axis='x',alpha=.15)
    save(fig,figures,'bootstrap_model_points')
    print(json.dumps({'status':'PASS','output_directory':str(figures),'figures':['defect_observables','E8_boundary_annuli','bootstrap_model_points']}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    main(parser.parse_args().directory)
