include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem4 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq

    predicate Increasing(xs: seq<int>) {
        forall i :: 0 <= i < |xs|-1 ==> xs[i] <= xs[i+1]
    }    

    predicate Inc(xs: seq<int>) {
        if |xs| > 1 then xs[0] <= xs[1] && Inc(xs[1..]) else true
    }

    predicate LastNotZer0(xs: seq<int>) {
        if |xs| > 1 then xs[|xs|-1] >= xs[|xs|-2] else false
    }

    predicate DuplicateExists(xs: seq<int>) {
        exists i :: 0 <= i < |xs|-1 && xs[i] == xs[i+1] &&  (0 <= i - 1 ==> xs[i-1] != xs[i]) && (i+2 < |xs| ==> xs[i+2] != xs[i])
    }

    predicate HasDuplicate(xs: seq<int>) {
        if |xs| > 1 then xs[0] == xs[1] || HasDuplicate(xs[1..]) else false
    }

    method problem4_1(input: string) returns (x: int) {
        var pieces := Map(Integer, split(input,"-"));
        assume {:axiom} |pieces| == 2 && pieces[0] <= pieces[1];
        x := 0;
        // assert !Inc([7,7,7,7,7,0]);
        for i := pieces[0] to pieces[1] {
            var numString := toStr(i);
            var nums := Map(Integer, split(numString, ""));
            if Increasing(nums) && HasDuplicate(nums)  {
                print i,"\n";
                print "numString", numString, "\n";
                print "nums ", nums, "\n";
                x := x +1;
            }
        }
    }

    method problem4_2(input: string) returns (x: int) {
        var pieces := Map(Integer, split(input,"-"));
        assume {:axiom} |pieces| == 2 && pieces[0] <= pieces[1];
        x := 0;
        // assert !Inc([7,7,7,7,7,0]);
        expect DuplicateExists([1,1,1,1,2,2]);
        expect DuplicateExists([1,1,2,2,3,3]);
        expect !DuplicateExists([1,2,3,4,4,4]);
        expect DuplicateExists([3,3,4,5,6,7]);
        for i := pieces[0] to pieces[1] {
            var numString := toStr(i);
            var nums := Map(Integer, split(numString, ""));
            if Increasing(nums) && DuplicateExists(nums)  {
                print i,"\n";
                print "numString", numString, "\n";
                print "nums ", nums, "\n";
                x := x +1;
            }
        }
    }
}
