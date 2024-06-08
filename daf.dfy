method Triple (x: int ) returns (r: int)
 {
 if x == 0{
 r := 0;
 } else {
 var y := 2 * x;
 r := x + y;
 }
 assert r == 3 * x;
}

function Fib (n: nat) : nat {
     if n < 2 then n else Fib(n - 2) + Fib(n - 1)
 }

method identic(x: array<int>, n: int) returns (rez: bool)
    ensures rez == (forall i :: 0 <= i < n - 1 ==> x[i] == x[i + 1])
{
    var identical: bool := true;

    for i := 0 to n - 2 {
        if x[i] != x[i + 1] {
            identical := false;
            break;
        }
    }

    rez := identical;
}

method Triple1 (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 }

 
 method Main()
 {  t  = 30
    var t := Triple1 (10) ;
    warning
    var t := Triple2 (10) ;
    warning
    var t := Triple (10) ;
 }


 method Triple2 (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 assert r == 3 * x+1;
 }

method Triple (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 assert r == 3 * x;
 //assert r < 5;
 assert true ;
 }

method test (x: int , y: int ) returns (a: int )
{ assume (x==y) ;
 a:=x-y;
 assert (z ==0) ;

// x == y => x-y == 0;
{{x == y}}a := x − y{{a == 0}}
x = 4 ,y = 3 => F

// x = 100 => x este == 100
{{true}}x := 100{{x == 100}}
x := 1 => F

{{0 <= x < 100}}x := x + 1{{0 <= x <= 100}}
x := -2 => F

{{true}}x := 2 ∗ y{{y <= x}}
y = -1 => F

{{0 <= x}}x := x − 1{{0 <= x}}
x = 0 => F
}


method Callers()
{
  var result := Triple1(18);
  assert result < 100; 
}

method Triple1(x: int) returns (r: int)
  ensures r == 3 * x
{
  var y := 2 * x;
  r := x + y; 
}

method Triple2(x: int) returns (r: int)
  requires x % 2 == 0 // Preconditie
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y; 
}


method Triple3(x: int) returns (r: int)
  requires x % 6 == 0
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}

method Triple4(x: int) returns (r: int)
  requires x % 2 == 0 && x >= 0
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}