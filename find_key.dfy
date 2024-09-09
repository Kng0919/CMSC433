//Input can not be changed beside return value
method find(a:seq<int>, v:int) returns (index:int)
ensures v in a ==> 0 <= index < |a| && a[index] == v
ensures v !in a ==> index == -1
{
    index := 0;
    while index < |a|
    decreases |a| - index
    //|a| represent the length of a
    invariant 0 <= index <= |a|
    invariant v !in a[..index]
     {
        if a[index] == v{
            return index;
        }
        index := index + 1;
    }
    assert v !in a[..index];
    assert index == |a|;
    assert v !in a;
    index := -1; //Not found
}

method Main(){
    var s:=[3,6,8,2,3]
    var r:= find(s,8)
    print r,"\n";
}