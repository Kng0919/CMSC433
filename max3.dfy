method max3(a:int, b:int, c:int) returns (m:int)
ensures m>= a && m>= b && m>=c
ensures m== a || m == b || m == c
{
    if a >= b{
        m:= a;
    }else{
        m:= b;
    }

    if c >= m{
        m :=c;
    }
}

method test(){
    assert 20 == max3(5,3,20)
}

method main(){
    var x := max3(1,2,3)
    print("Max of 3 is ", x)
}