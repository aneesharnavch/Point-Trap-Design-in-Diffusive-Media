#!/usr/bin/env python3
"""Small deterministic floating-point examples; these are not formal proofs.

Only Python's standard library is used. Polynomial quadratures are evaluated
analytically. The nonuniform partition search is explicitly a finite search
and local refinement, with no claim of certified global optimality.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


def bisect_increasing(f, lo, hi, iterations=70):
    if not f(lo) <= 0 <= f(hi):
        raise ValueError('Root is not bracketed')
    for _ in range(iterations):
        mid = (lo + hi) / 2
        if f(mid) <= 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def affine_left(alpha, c):
    primitive = lambda t: (1-alpha)*t*t/2 + t**3/3 - alpha*t
    return primitive(c)-primitive(alpha)


def affine_right(c, beta):
    primitive = lambda t: beta*t + (beta-1)*t*t/2 - t**3/3
    return primitive(beta)-primitive(c)


def balanced_cell(alpha, beta):
    if not 0 <= alpha < beta <= 1:
        raise ValueError('A strict source cell is required')
    c = bisect_increasing(lambda t: affine_left(alpha,t)-affine_right(t,beta), alpha, beta)
    return c, (affine_left(alpha,c)+affine_right(c,beta))/2


def budget_root(widths, barriers, budget, mass=1):
    if budget <= 0 or mass <= 0 or any(w <= 0 for w in widths):
        raise ValueError('Positive budget, source mass and cell widths required')
    if abs(sum(widths)-1) > 1e-12:
        raise ValueError('Source widths must sum to one')
    largest = max(barriers)
    # Solve for excess above the largest barrier, avoiding an artificial
    # lower endpoint offset and its possible loss of a near-pole root.
    def residual(delta):
        if delta == 0:
            return -math.inf
        return budget/mass-sum(w/(delta+largest-r) for w,r in zip(widths,barriers))
    delta = bisect_increasing(residual, 0, mass/budget*(1+1e-14))
    return largest+delta


def partition_design(q, budget=2):
    cells=[balanced_cell(a,b) for a,b in zip(q,q[1:])]
    widths=[b-a for a,b in zip(q,q[1:])]
    height=budget_root(widths,[r for _,r in cells],budget)
    strengths=[w/(height-r) for w,(_,r) in zip(widths,cells)]
    return height,[c for c,_ in cells],strengths,[r for _,r in cells]


def affine_partition_search(grid=24):
    candidates=[]
    for i in range(1,grid-1):
        for j in range(i+1,grid):
            q=[0,i/grid,j/grid,1]
            candidates.append((partition_design(q)[0],q))
    coarse,q=min(candidates)
    step=1/grid
    for _ in range(12):
        proposals=[]
        for di in [-1,0,1]:
            for dj in [-1,0,1]:
                trial=[0,q[1]+di*step,q[2]+dj*step,1]
                if 0 < trial[1] < trial[2] < 1:
                    proposals.append((partition_design(trial)[0],trial))
        _,q=min(proposals);step/=2
    height,sites,strengths,barriers=partition_design(q)
    return {'medium':'a(x)=1/(1+x), rho(x)=1, L=1', 'count':3,'budget':2,
            'coarse_grid_denominator':grid,'coarse_candidates':len(candidates),'refinement_stages':12,
            'coarse_best_height':coarse,'partition':q,'sites':sites,'strengths':strengths,
            'candidate_height':height,'barriers':barriers,
            'rigorous_formula_lower_bound':0.5+1/(8*9),
            'numerical_upper_candidate_only':True,
            'budget_residual':abs(sum(strengths)-2),
            'maximum_cell_balance_residual':max(abs(affine_left(a,c)-affine_right(c,b))
              for a,b,c in zip(q,q[1:],sites))}


def linear_solve(matrix, rhs):
    a=[list(row)+[v] for row,v in zip(matrix,rhs)];n=len(a)
    for k in range(n):
        p=max(range(k,n),key=lambda i:abs(a[i][k]))
        if abs(a[p][k]) < 1e-14:raise ValueError('Singular test system')
        a[k],a[p]=a[p],a[k];v=a[k][k]
        a[k]=[z/v for z in a[k]]
        for i in range(n):
            if i!=k:
                v=a[i][k];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
    return [row[-1] for row in a]


def graph_example():
    # Tail, head, length, conductance, density. The final two edges add a
    # genuine parallel edge and a loop; vertex3 is a passive reflecting tip.
    edges=[(0,1,.7,1.2,1.1),(1,2,.8,.9,.8),(1,3,.6,1.1,1.3),
           (0,1,.4,.8,.9),(1,1,.5,1.4,1.2)]
    strengths=[2,0,1,0];n=4
    matrix=[[0.]*n for _ in range(n)];rhs=[0.]*n;degree=[0]*n
    for v,k in enumerate(strengths):matrix[v][v]=k
    for tail,head,length,a,rho in edges:
        conductance=a/length;mass=rho*length
        matrix[tail][tail]+=conductance;matrix[head][head]+=conductance
        matrix[tail][head]-=conductance;matrix[head][tail]-=conductance
        rhs[tail]+=mass/2;rhs[head]+=mass/2
        degree[tail]+=1;degree[head]+=1
    values=linear_solve(matrix,rhs)
    profiles=[];maximum=max(values);mass=sum(r*l for _,_,l,_,r in edges)
    for tail,head,length,a,rho in edges:
        j0=a*(values[head]-values[tail])/length+rho*length/2
        vertex=max(0,min(length,j0/rho))
        maximum=max(maximum,values[tail]+j0/a*vertex-rho/(2*a)*vertex**2)
        profiles.append((tail,head,length,a,rho,j0))
    costs=[];adjusted=[];masses=[];reflecting=[];flux=[0.]*n
    for tail,head,length,a,rho,j0 in profiles:
        chi=4 if any(degree[v]==1 and strengths[v]==0 for v in [tail,head]) else 1
        integral_u=values[tail]*length+j0*length**2/(2*a)-rho*length**3/(6*a)
        energy=(j0*j0*length-j0*rho*length**2+rho*rho*length**3/3)/a
        costs.append(rho*(maximum*length-integral_u)+energy)
        adjusted.append(chi*length/a);masses.append(rho*length)
        flux[tail]+=j0;flux[head]+=rho*length-j0
        if chi==4:reflecting.append(abs(j0 if degree[tail]==1 else j0-rho*length))
    budget=sum(strengths);capacity=sum(1/r for r in adjusted)
    reaction=sum(k*(u-mass/budget)**2 for k,u in zip(strengths,values))/mass
    profile=sum(j-r*m*m/8 for j,r,m in zip(costs,adjusted,masses))/mass
    resistance=sum((r*m-mass/capacity)**2/r for r,m in zip(adjusted,masses))/(8*mass)
    lhs=maximum-mass/budget-mass/(8*capacity)
    return {'vertices':n,'edges':edges,'strengths':strengths,'vertex_values':values,
       'maximum':maximum,'source_mass':mass,'reaction_budget':budget,
       'source_conservation_residual':abs(sum(k*u for k,u in zip(strengths,values))-mass),
       'vertex_balance_residual':max(abs(f-k*u) for f,k,u in zip(flux,strengths,values)),
       'linear_system_residual':max(abs(sum(a*u for a,u in zip(row,values))-b) for row,b in zip(matrix,rhs)),
       'passive_flux_residual':max(reflecting),
       'deficit_left':lhs,'reaction_deficit':reaction,'edge_deficit':profile,
       'resistance_deficit':resistance,'deficit_identity_residual':abs(lhs-reaction-profile-resistance)}


def spectral_example(strengths, length=1.3, diffusivity=.7):
    n=len(strengths)
    f=lambda k: -n*math.pi if k==0 else length*k-2*sum(math.atan(s/(2*diffusivity*k)) for s in strengths)
    k=bisect_increasing(f,0,n*math.pi/length)
    angles=[math.atan(s/(2*diffusivity*k)) for s in strengths]
    cells=[2*a/k for a in angles];sites=[];left=0
    for d in cells:sites.append(left+d/2);left+=d
    mass=sum(d/2+math.sin(k*d)/(2*k) for d in cells)
    gradient=diffusivity*k*k*sum(d/2-math.sin(k*d)/(2*k) for d in cells)
    reaction=sum(s*math.cos(a)**2 for s,a in zip(strengths,angles))
    return {'length':length,'diffusivity':diffusivity,'strengths':strengths,
        'root':k,'eigenvalue':diffusivity*k*k,'sites':sites,'cells':cells,
        'phase_residual':abs(f(k)),'length_residual':abs(sum(cells)-length),
        'jump_residual':max(abs(2*diffusivity*k*math.sin(a)-s*math.cos(a)) for s,a in zip(strengths,angles)),
        'rayleigh_quotient':(gradient+reaction)/mass,
        'rayleigh_residual':abs((gradient+reaction)/mass-diffusivity*k*k),
        'minimum_state_value':min(math.cos(a) for a in angles)}


def run():
    c,r=balanced_cell(0,1);exact=math.sqrt(7/3)-1
    homogeneous=[]
    for n in [1,2,3,5]:
        L,D,K=1.7,.8,2.3
        barriers=[L*L/(8*D*n*n)]*n
        value=budget_root([1/n]*n,barriers,K,L)
        homogeneous.append({'n':n,'computed':value,'formula':L/K+L*L/(8*D*n*n),
                             'residual':abs(value-(L/K+L*L/(8*D*n*n)))})
    result={'purpose':'deterministic numerical validation, not formal verification',
      'arithmetic':'Python binary64; no interval-arithmetic certification',
      'bisection_iterations':70,'absolute_residual_tolerance':1e-10,
      'deficit_sign_tolerance':1e-12,
      'affine_one_trap':{'center':c,'exact_center_formula':exact,'barrier':r,
                         'center_error':abs(c-exact),'balance_residual':abs(affine_left(0,c)-affine_right(c,1))},
      'homogeneous':homogeneous,'partition_search':affine_partition_search(),
      'graph':graph_example(),'spectral_prescribed':spectral_example([.5,1.,2.5]),
      'spectral_uniform':spectral_example([4/3]*3)}
    residuals=[result['affine_one_trap']['center_error'],result['affine_one_trap']['balance_residual']]
    residuals += [r['residual'] for r in homogeneous]
    residuals += [v for k,v in result['graph'].items() if k.endswith('_residual')]
    residuals += [v for k,v in result['partition_search'].items() if k.endswith('_residual')]
    for field in ['spectral_prescribed','spectral_uniform']:
        residuals += [v for k,v in result[field].items() if k.endswith('_residual')]
        assert result[field]['minimum_state_value']>0
    assert max(residuals)<1e-10
    assert result['spectral_prescribed']['eigenvalue']<result['spectral_uniform']['eigenvalue']
    assert min(result['graph'][x] for x in ['reaction_deficit','edge_deficit','resistance_deficit'])>-1e-12
    result['maximum_reported_residual']=max(residuals)
    result['all_validation_checks_passed']=True
    return result


def num(x):
    if x==0:return '0'
    if abs(x)<1e-4:
        s=f'{x:.3e}';a,b=s.split('e');return a+r'\times10^{'+str(int(b))+'}'
    return f'{x:.10g}'


def latex(results):
    g=results['graph'];s=results['spectral_prescribed'];u=results['spectral_uniform'];p=results['partition_search']
    rows=[('Affine one-trap center error',results['affine_one_trap']['center_error']),
          ('Homogeneous formula: largest error',max(x['residual'] for x in results['homogeneous'])),
          ('Graph conservation residual',g['source_conservation_residual']),
          ('Graph vertex-balance residual',g['vertex_balance_residual']),
          ('Graph three-part deficit residual',g['deficit_identity_residual']),
          ('Spectral phase-equation residual',s['phase_residual']),
          ('Spectral cosine Rayleigh residual',s['rayleigh_residual'])]
    table='\n'.join(label+' & $'+num(value)+'$ \\\\' for label,value in rows)
    return r'''\section{Deterministic validation results}
\label{sec:technical-validation}
The accompanying \LeanFile{scripts/validate_examples.py} was executed for this
publication release. It uses only Python's standard library and binary64
arithmetic. These computations check formulas and reconstruction conventions;
they do not enlarge the scope of the Lean theorems and do not certify a
floating-point global optimum. No Monte Carlo estimate is used.
\begin{center}\begin{tabular}{lr}\toprule
Quantity & Absolute residual\\\midrule
'''+table+r'''
\bottomrule\end{tabular}\end{center}
The graph example has four vertices and five edges, including a loop, a
parallel pair, and a passive leaf. The linear solve gives
$M='''+num(g['maximum'])+r'''$, source mass $V='''+num(g['source_mass'])+r'''$
and budget $K=3$. The three deficit terms are respectively
$'''+num(g['reaction_deficit'])+r'''$, $'''+num(g['edge_deficit'])+r'''$,
and $'''+num(g['resistance_deficit'])+r'''$. Their independent sum reproduces
the observed gap above the sharp mass--resistance bound.

For $L=1.3$, $D=0.7$ and prescribed strengths $(0.5,1,2.5)$, the scalar phase
root gives $\lambda='''+num(s['eigenvalue'])+r'''$. With the same budget and
three equal strengths, the value is $'''+num(u['eigenvalue'])+r'''$.
The assembled cosine state remains positive; direct integration of its
squared derivative, squared value and contact terms reproduces the
Rayleigh quotient shown in the table.

For $a(x)=1/(1+x)$, $\rho(x)=1$, $L=1$, $N=3$ and $K=2$, a grid with
24 subdivisions followed by twelve local refinement stages gives the
candidate partition
\[
(q_0,q_1,q_2,q_3)=(0,'''+num(p['partition'][1])+','+num(p['partition'][2])+r''',1)
\]
and reconstructed height $'''+num(p['candidate_height'])+r'''$.
This is a numerical candidate with a measured budget residual; no
interval-certified feasible enclosure is claimed. The uniform lower weight bound gives
$M\geq 1/2+1/72\approx '''+num(p['rigorous_formula_lower_bound'])+r'''$ analytically;
the search does not close that gap or prove that its candidate is the
minimizer. The global existence and reconstruction theorem remains the
separate exact result.

Every input, output, tolerance and residual is recorded in
\LeanFile{source-bundle/validation/results.json}. The driver itself is included
in full in the source release and can be rerun without third-party packages.
'''


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    root=Path(__file__).resolve().parent.parent
    bundled=(root/'manifest.json').is_file()
    ap.add_argument('--output',type=Path,default=root/('validation/results.json' if bundled else 'source-bundle/validation/results.json'))
    ap.add_argument('--tex',type=Path,default=root/('validation/results.tex' if bundled else 'content/technical-validation.tex'))
    args=ap.parse_args();result=run()
    result['driver_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.tex.parent.mkdir(parents=True,exist_ok=True);args.tex.write_text(latex(result))
    print(json.dumps({'all_checks_passed':True,'maximum_residual':result['maximum_reported_residual'],
                      'results':str(args.output),'tex':str(args.tex)}))

if __name__=='__main__':main()
