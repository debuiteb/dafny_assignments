method isPrefix(pre: string, str: string) returns (res:bool)
requires |pre| > 0 && |str| > 0 && |str|>= |pre|
{
    var i : int := 0;
    var count : int := 0;
    while (i <  |pre|) decreases (|pre| - i)
    {
        if str[i] == pre[i] {
            count := count +1;
        }
        i := i + 1;
   }
   res:= false;
   
   if count == |pre| {
       res := true;
   }
}
