\\ Exact obstruction to a one-root reconstruction in the spurious order-5 field.
default(parisizemax,2000000000);
hi_diagonal_kummer_check() = {
my(P,nf,r,d,r2,roots,primes,ramification);
P=z^8+z^7-2*z^6+5*z^5-9*z^4-60*z^3+2*z^2+12*z+1;
nf=nfinit(P);
r=Mod(z,P);
d=-(r^4-2*r^3+r+1)/(r^3+r^2+3*r+5);
if(d^2-5*d-1!=0,error("incorrect quadratic embedding"));
r2=((d-6)*r^3+(6-d)*r^2+(13-3*d)*r+3-3*d)/5;
if(r^4+(d-2)*r^3+d*r^2+(3*d+1)*r+d^2!=0,error("incorrect row polynomial"));
roots=nfroots(nf,x^5-d*r^2*r2);
if(type(roots)!="t_COL",error("root calculation did not return a column"));
if(#roots,error("unexpected Kummer root inside the row field"));
print("[ok] absolute row field degree=",poldegree(P),", signature=",nf.sign);
print("[ok] W^5=d*r^2*r2 has no root inside this field");
if(nf.disc!=5^5*29^4,error("unexpected discriminant"));
primes=idealprimedec(nf,5);
ramification=vector(#primes,j,[lift(nfmodpr(nf,d,primes[j])),primes[j].e,primes[j].f]);
if(ramification!=[[1,4,1],[4,2,2]],error("unexpected local ramification"));
print("[ok] discriminant=5^5*29^4; [d mod P,e,f]=",ramification);
print("[ok] both primes above 5 ramify, so this is not the prescribed single-prime ray field");
print("EXACT DIAGONAL KUMMER OBSTRUCTION PASSED");
};
hi_diagonal_kummer_check();
quit;
