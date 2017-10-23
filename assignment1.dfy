method isPrefix(pre: string, str: string) returns (res:bool)
requires |pre| > 0 && |str| > 0
{

    res:=true;
    forall (i:=0 | i < |pre|) ensures i < |pre| {
        if pre[i] != str[i] {
           res := false;
        }

    }

    if x == |pre| {
        res := true;
    }
    else{
        res := false; 
    }

  /*
    char  [] str;
    char [] pre;

    while(x<pre.length){
        if(pre[x]!=str[x]){
            return false;
        }
    }
    return true;

  */
}