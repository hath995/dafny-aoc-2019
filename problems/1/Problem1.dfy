include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem1 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    
    method parseInput(input: string) returns (s: seq<int>) {
        var res := splitOnBreak(input);
        s := Map(xs => Integer(xs), Filter(xs => xs != "", res));
    }

    function sum(s: seq<int>): int {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }

    function calcFuel(x: int): int {
        (x/3)-2
    }

    function recCaclFuel(x: int, partialSum: int): int {
        var fuel := calcFuel(x);
        if fuel > 0 then recCaclFuel(fuel, partialSum + fuel) else partialSum
    }

    method problem1_1(input: string) returns (x: int)
    {
        var data := parseInput(input);
        return sum(Map(calcFuel, data));
    }

    method problem1_2(input: string) returns (x: int)
    {
        var data := parseInput(input);
        var partial := Map(x => recCaclFuel(x,0), data);
        print partial;
        return sum(partial);
    }
}