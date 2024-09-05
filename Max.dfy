method Max(a: int, b:int) returns (max:int)
ensures max >= a && max >= b
{
if a > b{
    max := a;
}
else{
    max:= b;
}
}