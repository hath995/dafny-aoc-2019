include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem5 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    method parseInput(input: string) returns (result: seq<int>) {
        var res := Split.split(input, ",");
        result := Map(Integer, res);
    }


    datatype ParameterMode = Position(pos: nat) | Immediate(pos: nat)
    // datatype OpcodeParam = NullaryOp | UnaryOp(apm: ParameterMode) | BinaryOp(apm: ParameterMode, bpm: ParameterMode) | TernaryOp(apm: ParameterMode, bpm: ParameterMode, cpm: ParameterMode)
    datatype Opcode = Add(apm: ParameterMode, bpm: ParameterMode, cpm: ParameterMode) | Mul(apm: ParameterMode, bpm: ParameterMode, cpm: ParameterMode) | Input(apm: ParameterMode) | Output(apm: ParameterMode) | Halt
    // function op2Opcode(x: int): Opcode {

    // }

    function fillZero(params: seq<char> ): seq<char> 
        requires |params| <= 3
        decreases 3-|params|
    {
        if |params| == 3 then params else fillZero(['0']+params)
    }

    method parseOpcode(opCode: int) returns (opId: int, params: seq<char>) {
        var opString := String(opCode);
        assume {:axiom} 1 <= |opString| <= 5;
        expect 1 <= |opString| <= 5;
        opId:=0;
        params := [];
        match |opString| {
            case 1 => {
                opId := Integer(opString);
                params := fillZero([]);
            }
            case 2 => {
                opId := Integer(opString);
                params := fillZero([]);
            }
            case _ => {
                opId := Integer(opString[|opString|-2..]);
                params := fillZero(opString[..|opString|-2]);
            }
        }

        
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
    method problem5_1(input: string) returns (x: int) {
        var result := toStr(0);
        print result,"\n";
        print String(-123),"\n";
        print String(1002),"\n";
        print String(0),"\n";
        print String(123456789),"\n";
        return 3;
    }

    method problem5_2(input: string) returns (x: int) {
        return 4;
    }

    export provides problem5_1, problem5_2
}
