function Mult(x:nat, y:nat):nat{
    if y == 0 then 0 else x + Mult(x,y-1);
}

lemma Multi_Comm(x:nat, y:nat)
ensures Mult(x,y) == Mult(y,x)
{
    if x == y{}
    else if x == 0{
        Multi_Comm(x,y-1);
    }
    else if y == 0{
        Multi_Comm(x-1,y);
    }
    else{
        // x > 0, y > 0
        calc{
            Mult(x,y);
            ==
            x + Mult(x, y-1);
            ==
            {Multi_Comm(x,y-1);}
            x + Mult(y-1,x);
            ==
            x + y - 1 + Mult(y-1,x-1);       
            ==     
            {Multi_Comm(x-1,y-1);}
            x + y - 1 + Mult(x-1,y-1);
            y + Mult(x-1,y);
            ==
            y + Mult(y,x-1);
            ==
            Mult(y,x);
        }
    }
}