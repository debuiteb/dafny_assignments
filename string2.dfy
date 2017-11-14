predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

predicate isSubstringPred(sub:string, str:string)
{
  (|sub| <= |str|) &&	(exists i,j : int :: (0 <= i <= |str| &&  0 <= j <= |str| ) && (j-i) == |sub|  && (sub == str[i..j]  ) )	 //(exists s : string :: isPrefixPred(sub,str))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	!(|sub| <= |str|) || (forall i,j : int :: (0 <= i<= |str| &&  0 <= j <= |str| )  && (j-i) == |sub|  ==> (sub != str[i..j]  ))
}


// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	(k <= |str1| && k <= |str2|) && (exists sub : string :: (|sub| == k) && isSubstringPred(sub,str1) && isSubstringPred(sub,str2) )
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	(k > |str1| || k > |str2|) || (forall sub : string :: (|sub| == k) ==> ((isNotSubstringPred(sub,str1) || isNotSubstringPred(sub,str2) ) ) )
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
