function add (x: nat, y: nat): nat
{
  if (y == 0) then x
  else add (x, y-1) + 1
}




















method -lus_ine(x:int) returns (r:int)
  requires x >= 0;
  ensures r == x + 1;
 {
 returns x + 1;
 }





method add_by_one(x:int,y:int) returns(r:int)
{
assume(y >= 0);
var i = 0;
r = x;

#invariant true before enter loop. Requires
assert(0<=i <= y)
assert(r == x + i)

r =*;
i =*;
assume(i >= 0); #must be added to invariant

#make sure sat inv and arbitrary, from this state. Ensures
assume(0<= i <= y)
assume(r == x + i)

###################################(If false), still keep inv
while( i < y) i
  
  invariant 0 <= i <= y;;
  invariant r == x + i;
  decrease y - i;
{
  var t = y - i;
  r = r + 1;
  i = i + 1; #(Added var w = *; assert(i >= 0); assume(w == i + 1) )
                     
             # i = plus_one(i)  OR
             # w = plus_one(i)
             # i = w--> need pre-condition to make sure it is true, otherwise, raise error
  assert(y-i >= 0);
  assert(y-i < t);
 #invariant true in loop
  assert(0 <= i <= y);
  assert(r == x + i);
  assume(false);
}
####################################

assert(r == x + y);
return r;
}
































lemma zero_add_lemma (x: nat)
  ensures add (0, x) == x
{
  if (x == 0) {}
  else {
    calc {
      add(0,x);
      add(0,x-1) + 1;
      { zero_add_lemma(x-1);}  #simplifies
      x-1 + 1;
      x
    }
   }
}

lemma add_zero_lemma (x: nat)
  ensures add (x, 0) == x
{
  assume (false);
}

lemma add_plus_one (x: nat, y: nat)
  ensures add(x, y) + 1 == add(x, y+1);
{
  calc{
    add(x,y+1);
    add(x,y+1-1) + 1;
    add(x,y) + 1;
    }
  if (y == 0) {}
  else {
    calc{ #???
      add(x,y) + 1;
      add(x,y+1);
      { add_plus_one(x,y); }
      add(x,y)
}


lemma one_plus_add (x: nat, y: nat)
  ensures add(x, y) + 1 == add (x+1, y)
{
  if (y == 0) {}
  else{
  calc{
    add(x,y)+1     #lhs
    add(x,y-1)+1+1 #rhs
    {one_plus_add(x,y-1);)
    add(x+1,y-1) + 1
    add(x+1,y)
}



lemma add_comm_lemma (x: nat, y: nat)
  ensures add (x, y) == add (y, x);
{
  if (y==0){}
  else{
    calc{
      add(x,y);
      add(x,y-1)+1; #change 1 ->>3 complain
      {add_comm_lemma(x,y-1)} #IH
      add(y-1,x)+1; #outcome
      { one_plus_add(y-1,x);} # without this, dfny still can prove it
      add(y,x);
}
#assume(flase) unfinished proof
