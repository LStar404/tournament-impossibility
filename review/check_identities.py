from fractions import Fraction
from math import factorial

def extrema(n):
    edges=[(i,j) for i in range(n) for j in range(i+1,n)]
    best=0
    for code in range(1<<len(edges)):
        pred=[0]*n
        for e,(i,j) in enumerate(edges):
            if (code>>e)&1: pred[j]|=1<<i
            else: pred[i]|=1<<j
        dp=[[0]*n for _ in range(1<<n)]
        for j in range(n):dp[1<<j][j]=1
        for mask in range(1,1<<n):
            for j in range(n):
                if not ((mask>>j)&1):continue
                prev=mask^(1<<j)
                k=prev&pred[j]
                while k:
                    bit=k&-k;i=bit.bit_length()-1;k-=bit
                    dp[mask][j]+=dp[prev][i]
        best=max(best,sum(dp[-1]))
    return best
P={n:extrema(n) for n in range(1,7)}
a={n:Fraction(P[n]*2**(n-1),factorial(n)) for n in P}
m={n:n*n*a[n]-(2*a[n//2] if n%2==0 else 0) for n in P}
for n in P:
    j=0; v=n
    while v%2==0:j+=1;v//=2
    recovered=sum(Fraction(2**(k*(k+2)),n**(2*k+2))*m[n//2**k] for k in range(j+1))
    assert recovered==a[n]
print('P',P,'a',a,'m',m)
def nu(n):
    v=0
    while n%2==0:v+=1;n//=2
    return v
def s(n): return -sum(Fraction(2**(j*(j+1)),n**(2*j+1)) for j in range(nu(n)))
for n in range(1,4097):
    assert n*n*s(n)-(2*s(n//2) if n%2==0 else 0)==(-n if n%2==0 else 0)
print('Appendix E identity checked n=1..4096')
