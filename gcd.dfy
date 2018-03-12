function gcd(m: nat, n: nat): nat
{
  if (n==m) then n
  else if (m>n) then gcd(m-n, n)
  else gcd(m, n-m)
}














lemma gcd_lemma(m: nat, n:nat)
  requires m >= 1 and n >= 1 #requires are true, then it is the assumption
  ensures gcd(m,n) == gcd(n,m)
  {
  }


/*
method GcdCal(m: nat, n: nat) returns (res: nat)
  ensures res == gcd(m, n);

{
  var m1: nat, n1: nat := m, n;
  
  
  #assume gcd(m,n) == gcd(n,m); # non-determinstic no concrete value, cannot check
  gcd_lemma(m,n); #debug 
  
  while (m1!=n1)
  invariant n1 >= 1;
  invariant m1 >= 1;
  invariant gcd(m,n) == gcd(n1,m1)
  decrease m1 + n1;
  {
    if (m1>n1) {
      m1 := m1-n1;
    }
    else {
      n1 := n1-m1;
    }
 }
 return m1;
}
 */









/* gcd lemma: use gcd(m, n) = gcd(n1, m1) */
