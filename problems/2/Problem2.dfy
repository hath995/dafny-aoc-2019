include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem2 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    method parseInput(input: string) returns (s: seq<int>) {
        var res := Split.split(input, ",");
        s := Map(Integer, res);
    }

    method executeIntcodes(intcodes: array<int>) 
        modifies intcodes
        requires intcodes.Length > 0
    {
        var i:=0;
        // print "here";
        while i < intcodes.Length {
            match intcodes[i] {
                case 1 => {
                    assume {:axiom} i+4 < intcodes.Length;
                    var pos1 := intcodes[i+1];
                    var pos2 := intcodes[i+2];
                    var dest := intcodes[i+3];
                    assume {:axiom} 0 <= pos1 < intcodes.Length;
                    assume {:axiom} 0 <= pos2 < intcodes.Length;
                    assume {:axiom} 0 <= dest < intcodes.Length;
                    intcodes[dest]:=intcodes[pos1]+intcodes[pos2];
                    i := i + 4;
                }
                case 2 => {
                    assume {:axiom} i+4 < intcodes.Length;
                    var pos1 := intcodes[i+1];
                    var pos2 := intcodes[i+2];
                    var dest := intcodes[i+3];
                    assume {:axiom} 0 <= pos1 < intcodes.Length;
                    assume {:axiom} 0 <= pos2 < intcodes.Length;
                    assume {:axiom} 0 <= dest < intcodes.Length;
                    intcodes[dest]:=intcodes[pos1]*intcodes[pos2];
                    i := i + 4;
                }
                case 99 => {
                    break;
                }
                case _ => {
                    print "Error: encounted bad incode", intcodes[i], i, "\n";
                    break;
                }
            }
        }
    }

    method problem2_1(input: string) returns (x: int) {
        var data:= parseInput(input);
        assume {:axiom} |data| > 3;
        print data, "\n"; 
        var arr := ToArray(data);
        arr[1]:=12;
        arr[2]:=2;
        executeIntcodes(arr);
        return arr[0];
    }

    method problem2_2(input: string) returns (x: int) {
        var data:= parseInput(input);
        assume {:axiom} |data| > 3;
        print data, "\n"; 
        var noun := 0;
        while noun <= 99 {
            var verb := 0;
            while verb <= 99 {

                var arr := ToArray(data);
                arr[1]:=noun;
                arr[2]:=verb;
                executeIntcodes(arr);
                if arr[0] == 19690720 {
                    // print "got here", noun, verb;
                    return 100*noun + verb;
                }
                verb := verb + 1;
            }
            noun := noun + 1;
        }
        x := -1;
    }
}