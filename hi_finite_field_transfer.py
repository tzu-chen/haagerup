"""Check the characteristic-free cubic transfer identity and char-2 spectrum.

The identities in Section 60 are proved there uniformly. This script checks
the indexing off the Q/C locus, then the complete matrix consequences on
independently certified characteristic-2 rows at orders 3 and 9.
"""
import json
from pathlib import Path
import subprocess
import tempfile


GP = r'''
default(parisizemax,1000000000);
make_A(n,d,W)={
 matrix(n,n,g,h,if(g==1&&h==1,(d-2)/(d-1),
 if(g==1||h==1||g==h,-1/(d-1),W[g]*W[(h-g)%n+1]/W[h]/(d-1))));
};
check_transfer(n,d,A,complete)={
my(t=1/d,nn=n^2,U,V,W,Z,R,J,F,H,K,L,D,QQ,ErrR,ErrL,E,N,ff,ee,Pent,rt,mults);
U=vector(nn,i,(i-1)%n==0)~;
V=vector(nn,i,(i-1)\n==0)~;
W=vector(nn,i,A[(i-1)%n+1,(i-1)\n+1])~;
Z=vector(nn,i,A[(i-1)\n+1,(i-1)%n+1])~;
R=matrix(nn,nn,i,j,my(a=(i-1)\n,b=(i-1)%n,c=(j-1)\n,e=(j-1)%n);
 if(b==c,A[b+1,(a+e)%n+1],0));
J=matrix(nn,nn,i,j,my(a=(i-1)\n,b=(i-1)%n,c=(j-1)\n,e=(j-1)%n);
 if(a==e,A[(b+c)%n+1,a+1],0)-(a==0&&e==0));
QQ=matrix(n,n,g,h,sum(m=0,n-1,A[(g-1+m)%n+1,h]*A[h,m+1])-(g==1)+t*(h==1));
ErrR=matrix(nn,nn,i,j,my(a=(i-1)\n,b=(i-1)%n,c=(j-1)\n,e=(j-1)%n);
 if(b==e,QQ[(c-a)%n+1,b+1],0));
ErrL=matrix(nn,nn,i,j,my(a=(i-1)\n,b=(i-1)%n,c=(j-1)\n,e=(j-1)%n);
 if(a==c,QQ[(b-e)%n+1,a+1],0));
if(R*J-matid(nn)!=ErrR||J*R-matid(nn)!=ErrL,error("Q operator identity"));
F=matrix(nn,nn,i,j,my(a=(i-1)\n,b=(i-1)%n,c=(j-1)\n,e=(j-1)%n);
 sum(m=0,n-1,A[m+1,(b+c)%n+1]*A[b+1,(m+a)%n+1]*A[c+1,(m+e)%n+1])
 -A[(b+e)%n+1,a+1]*A[(c+a)%n+1,e+1]+t*(b==0&&c==0));
H=W*U~+V*Z~-V*U~-t*U*V~;
if(F!=R^3-J^2-H,error("off-solution C operator identity"));
if(!complete,
 if(QQ==0||F==0,error("off-solution sample unexpectedly satisfies all equations"));
 print("OFF-SOLUTION Q/C TRANSFER IDENTITIES PASSED n=",n);return);
if(QQ!=0||F!=0,error("certificate does not satisfy Q/C"));
K=Mat([U,V,W]);L=Mat([U,V,Z])~;
D=-t*(W*Z~+V*V~+U*U~-t*U*V~);
if(R^5-matid(nn)!=D,error("rank-three fifth defect"));
if(matrank(K)!=3||matrank(L)!=3||matrank(D)!=3,error("rank-three assertion"));
if(t^2+t+1,error("not characteristic-two dimension"));
if(matrank(L*K)!=1,error("Gram rank"));
ee=U+t*V+t^2*W;ff=t*U~+V~+t^2*Z~;
if(D^2!=ee*ff||matrank(D^2)!=1||D^3!=t*D^2,error("defect powers"));
E=t*D^2;N=D-t*E;
if(E^2!=E||R*E!=t*E||E*R!=t*E,error("spectral projection"));
if(N^2!=0||N*E!=0||E*N!=0||matrank(N)!=2,error("rank-two nilpotent"));
if(R^10!=matid(nn)+t^2*E||R^30!=matid(nn),error("order-thirty identity"));
if(R^15==matid(nn)||R^10==matid(nn)||R^6==matid(nn),error("order not exactly thirty"));
Pent=R*(matid(nn)+D);
if(Pent^5!=matid(nn)||Pent!=R^6,error("corrected pentagon"));
rt=ffprimroot(d)^(fforder(ffprimroot(d))/5);
mults=vector(5,j,nn-matrank(Pent-rt^(j-1)*matid(nn)));
print("Corrected pentagon eigen multiplicities: ",mults);
print("COMPLETE CHAR-2 TRANSFER CERTIFICATE n=",n,"; rank(R^5-I)=3, rank((R^5-I)^2)=1, rank(N)=2; order(R)=30");
};
run_certificate()={
my(n=data[1],f=Mod(1,2)*Polrev(data[3],t),z=ffgen(f,'z),d=subst(Polrev(data[4],t),t,z),R,P,A);
R=vector(n,a,subst(Polrev(data[5][a],t),t,z));
P=vector(n,a,z^0);for(a=2,n-1,P[a+1]=P[a]*R[a+1]);
A=matrix(n,n,g,h,if(g==1&&h==1,d-2,if(g==1||h==1||g==h,-1,
 if(g<h,P[h]/(P[g]*P[h-g+1]),d*P[h]*P[g-h+1]/P[g]))))/(d-1);
check_transfer(n,d,A,1);
};
run_off()={
my(z=ffgen(ffinit(2,4,'z)),gen=ffprimroot(z),d=gen^5,W,n=5);
W=[z^0,gen,gen^2,d/gen^2,d/gen];
check_transfer(n,d,make_A(n,d,W),0);
d=Mod(q0,q0^2-5*q0-1);W=[-1,2,3,d/3,d/2];
check_transfer(n,d,make_A(n,d,W),0);
};
'''


def main():
    with tempfile.TemporaryDirectory(prefix='hi_transfer_') as temp:
        path = Path(temp) / 'check.gp'
        commands = ['iferr(run_off(),e,print(e);quit(1));']
        for n, index in ((3, 0), (9, 0), (9, 1)):
            cert = Path(__file__).with_name('hi_finite_field_certificates') / f'hi_finite_field_{n}_char2_{index}.json'
            data = json.loads(cert.read_text())
            commands.append('data='+json.dumps(data)+';')
            commands.append('iferr(run_certificate(),e,print(e);quit(1));')
        path.write_text(GP+'\n'.join(commands)+'\nquit;\n')
        result = subprocess.run(['gp', '-q', '-f', str(path)], capture_output=True,
                                text=True, timeout=600)
        print(result.stdout, end='')
        if result.returncode or result.stdout.count('COMPLETE CHAR-2 TRANSFER CERTIFICATE') != 3:
            raise ArithmeticError(result.stdout+result.stderr)
    print('ALL TRANSFER IDENTITY AND CHARACTERISTIC-TWO SPECTRAL CHECKS PASSED')


if __name__ == '__main__':
    main()
