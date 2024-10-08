datatype List<T> = Nil | Cons(head: <T>>, tail:List<T>)

function length<T>(xs:List<T>) : (l:nat){
    match xs{
        case Nil => 0;
        case Cons(_, tail) => length(tail) + 1;
    }
}

function lengthTailCall<T>(xs:List<T>, acc:nat) : (l:nat)
ensures lengthTailCall(xs,acc) == length(xs) + acc
{
    match xs{
        case Nil => acc
        case Cons(_, tail) => lengthTailCall(tail, acc + 1)
    }
}

lemma length_correct<T>(xs:list<T>)
ensures lengthTailCall(xs,0) = length(xs)
{}


method length2<T>(xs:List<T>) returns (l:nat)
ensure length(xs) == l
{
    var lst := xs;
    var len := 0;
    while lst != Nil
    decreases length(lst)
    invariant length(lst) + len == length(xs)
    {
        len := len + 1;
        lst := lst.tail;
    }

    return len;
}

function get<T>(xs:List<T>, i:nat):(v:T)
requires i < length(xs)
ensures contains(xs,v)
{
    match xs{
        case Cons(h,t) => if i == 0 then h else get(t, i-1)
    }
}

function contains<T(==)>(xs:List<T>, v:T):bool{
    match xs{
        case Nil => false
        case cons(h,t) => v == h || contains(t,v)
    }
}

function List2Seq(xs:List<T>):(s: seq<T>)
ensures length(xs) == |s|
//ensures forall i:nat :: i < length(xs) ==> get(xs,i) in s
//ensures forall i:nat :: i < |s| ==> contains(xs,s[i])
ensures forall i:nat :: i < length(xs) ==> get(xs,i) == s[i]
{
    match xs{
        case Nil => []
        case Cons(h,t) => [h] + List2Seq(t)
    }
}


predicate is_sorted(xs:List<int>){
    match xs{
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(h,cons(h2,tail)) => if h1 < h2 then false
                else is_sorted(cons(h2,tail))
    }
}

function insert_sorted(v:int,xs:List):(l:List<int>)
requires is_sorted(xs)
ensures is_sorted(l)
ensures length(l) == length(xs) + 1
ensures contains(l, v)
ensures !contains(xs,v) ==> contains(l,v)
{ 
    match xs{
        case Nil => Cons(v, Nil)
        case Cons(h,t) => if v < h then Cons(v, xs) else Cons(h, insert_sorted(v,t))
    }
}

function insert(xs:List<T>, v: T, i:nat):(l:List<T>)
requires i <= length(xs)
ensures length(xs) + 1 == length(l)
ensures contains(l,v)
ensures get(l,i) == v
{
    if i == 0 then Cons(v,xs) else Cons(xs.head, insert(xs.tail, v, i - 1))
}


method Main(){
    var l := Cons(10, Cons(30, Nil));
    print l, "\n";
}