include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../parser/regex.dfy"
module Problem3 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened RegEx
    datatype Direction = Up | Right | Down | Left
    datatype Step = Step(step: nat, dir: Direction)
    datatype Point = Point(x: int, y: int)
    function abs(x: int): nat {
        if x < 0 then -x else x
    }

    function manhattanDist(p1: Point, p2: Point): int {
        abs(p1.x-p2.x) + abs(p1.y-p2.y)
    }

    method parseInput(input: string) returns (s: seq<seq<Step>>)
        decreases * 
    {
        s := [];
        var lines := Filter(x => x != "", splitOnBreak(input));
        for i := 0 to |lines| {
            var stepsStrings := split(lines[i],",");
            var steps: seq<Step> := [];
            for k := 0 to |stepsStrings| {

                var matches, captures := ReMatch("(U|R|D|L)((1|2|3|4|5|6|7|8|9|0)+)", stepsStrings[k]);
                expect matches;
                assume {:axiom} |captures| == 3;
                var step := match captures[1] {
                    case "U" => Step(abs(Integer(captures[2])), Up)
                    case "R" => Step(abs(Integer(captures[2])), Right)
                    case "L" => Step(abs(Integer(captures[2])), Left)
                    case "D" => Step(abs(Integer(captures[2])), Down)
                    case _ => Step(0, Down)
                };
                steps := steps + [step];
            }
            s := s + [steps];
        }
    }

    function step(d: Direction, p: Point): Point {
        match d {
            case Up => Point(p.x, p.y+1)
            case Down => Point(p.x, p.y-1)
            case Left => Point(p.x-1, p.y)
            case Right => Point(p.x+1, p.y)
        }
    }

    method findNearest(data: seq<seq<Step>>) returns (x: int)

    {
        var linePoints : set<Point> := {};
        var intersections: set<Point> := {};
        for i := 0 to |data| {
            var pos := Point(0,0);
            for k := 0 to |data[i]| {
                for j:= 0 to data[i][k].step {
                    pos := step(data[i][k].dir, pos);
                    if i == 0 {
                        linePoints := linePoints + {pos};
                    }else{
                        if pos in linePoints {
                            intersections := intersections + {pos};
                        }
                    }
                }
            }
        }
        var origin := Point(0,0);
        var d := -1;
        print intersections;
        while intersections != {} {
            var px :| px in intersections;
            var distance := manhattanDist(px, origin);
            if d == -1 {
                d := distance;
            }else if distance < d {
                d := distance;
            }
            intersections := intersections - {px};
        }
        return abs(d);
    }

    method findFastest(data: seq<seq<Step>>) returns (x: int)

    {
        var linePoints : set<Point> := {};
        var pointDist : map<Point, nat> := map[];
        var intersections: set<nat> := {};
        for i := 0 to |data| {
            var pos := Point(0,0);
            var dist := 0;
            for k := 0 to |data[i]| {
                for j:= 0 to data[i][k].step {
                    pos := step(data[i][k].dir, pos);
                    dist := dist + 1;
                    if i == 0 {
                        linePoints := linePoints + {pos};
                        pointDist := pointDist[pos := dist];
                    }else{
                        if pos in linePoints && pos in pointDist {
                            intersections := intersections + {dist+pointDist[pos]};
                        }
                    }
                }
            }
        }
        var origin := Point(0,0);
        var d: int := -1;
        print intersections;
        while intersections != {} {
            var px :| px in intersections;
            if d == -1 || px < d {
                d := px;
            }
            intersections := intersections - {px};
        }
        return abs(d);
    }

    method problem3_1(input: string) returns (x: int)
        decreases *
    {
        var data := parseInput(input);
        // print data;
        var dist := findNearest(data);
        return dist;
    }

    method problem3_2(input: string) returns (x: int)
        decreases *
    {
        var data := parseInput(input);
        // print data;
        var dist := findFastest(data);
        return dist;
    }

    export provides problem3_1, problem3_2
}
