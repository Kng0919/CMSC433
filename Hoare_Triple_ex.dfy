method test1(a: int, b: int) returns (r:int)
ensures r == 1
{
    var x := a;
    assume{:axiom} x == 0;
    x := x+1;
    assert x == 1;

    return x;
}

method test2(a:int,b:int) returns (r:int){
    var i,j := a,b;
    assume{:axiom} i > j
    assert i > j;
    i := i+1
    assert i > j+1;
    j := j+1
    assert i > j
}

method test3(a:int) returns (r:int){
    var x := a;
    assume{:axiom} x == 2;
    assert x == 2 => x > 1;
    assert x > 1
    assert x + 1 > 0;
    x := x + 1;
    assert x > 0;
}

// {false} x:=x+1; {x>100} valid

//{z = y + 1} x := z * 2 {x = 4}
method test4(a:int, b:int,c:int){
    var x,y,z := a , b , c;
    assume{:axiom} z == y + 1;
    assume z == 2;
    assert z * 2 == 4;
    x:= z * 2;
    assert x == 4;
}


method test5(a:int, b:int)
requires a + 1 <= b;
{
    var x, n:= a,b;
    //assume x + 1 <= n
    assert x + 1 <= n; //P
    x := x + 1; //S
    assert x <= n; //Q
}

/*
Find weakest precondition P
{P} x:=3 {x+y>0}

(x+y>0)[3/x]
= 3 + y > 0
= y >-3
{y > -3} x:=3{x+y>0}
*/

//{x >= 0} x := x + 3; x := 2 * x {x >= 6}
method test6(a:int, b:int){
    var x, y := a ,b;
    assume 2 * (x+3) >= 6;
    assert 2 * x >= 0;
    assert x >= 0;
    x:= x+ 3;
    assert 2 * x >= 6;
    x := 2 * x;
    assert x >= 6;
}

/* Conditionals
{ true }
if x <= 0
{y := 2}
else
{y := x + 1}
{x <= y}
*/
method test7(a: int,b: int){
    assert true;
    if x <= 0
    {   assert x <= 0;
        y := 2;   
        assert x <= 0 && y == 2;
            }
    else
    { 
        assert x > 0
        y := x + 1; 
        assert x > 0 && y == x + 1;
        }

    assert x <= 0 ==> y == 2 ==> x < y;
    assert x > 0 ==> y == x + 1 ==> x < y;
    assert (x <= 0 && y == 2) || (x > 0 && y == x + 1);
    assert x <= y;
}


// {x = y} x := y * 2 {x = x * 2}
method test8(a:int, b:int){
    var x,y := a, b;

    //assume x == y;
    assert x == y;
    assert y * 2 == y * 2;
    x := y * 2;
    assert x == 2 * y;
}
//{x + 3 = z} x := x + 3 {x = z}
//{y * (x+1) = 2 * z} x:= x + 1; y:= y * x{y = 2 * z}
//{x > 0} 
method test9(){
    if(x>0) then y := x else y:= 0 {y > 0}
}