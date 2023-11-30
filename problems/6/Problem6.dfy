include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem6 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq

    datatype Matrix = Matrice(vals: seq<seq<int>>, rows: nat, columns: nat)

    predicate isMatrix(mat: Matrix) {
        mat.rows >= 1 && mat.columns >= 1 && |mat.vals| == mat.rows && forall i :: 0 <= i < mat.rows ==> |mat.vals[i]| == mat.columns
    }

    function seqTranspose(mat: Matrix): Matrix
        requires isMatrix(mat)
        ensures isMatrix(seqTranspose(mat))
        ensures seqTranspose(mat).columns == mat.rows
        ensures seqTranspose(mat).rows == mat.columns
    //     ensures seqTranpose(matrix).Length0 == matrix.Length1 && ftranspose(matrix).Length1 == matrix.Length0
        ensures forall i, j :: 0 <= i < mat.columns && 0 <= j < mat.rows ==> seqTranspose(mat).vals[i][j] == mat.vals[j][i]
    {
        Matrice(seq(mat.columns, i requires 0 <= i < mat.columns => seq(mat.rows, j requires 0 <= j < mat.rows => mat.vals[j][i])), mat.columns, mat.rows)
    }

    function matAdd(left: Matrix, right: Matrix): Matrix
        requires isMatrix(left) && isMatrix(right)
        requires left.rows == right.rows
        requires left.columns == right.columns
        ensures isMatrix(matAdd(left,right))
        ensures matAdd(left,right).rows == left.rows && matAdd(left, right).columns == left.columns
        ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matAdd(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
    {
        Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(left.columns, j requires 0 <= j < left.columns => left.vals[i][j] + right.vals[i][j])), left.rows, left.columns)
    }

    function Sum(vals: seq<int>): int
    {
        if |vals| == 0 then 0 else vals[0] + Sum(vals[1..])
    }

    function matMul(left: Matrix, right: Matrix): Matrix
        requires isMatrix(left) && isMatrix(right)
        requires left.columns == right.rows
        ensures isMatrix(matMul(left,right))
        ensures matMul(left,right).rows == left.rows && matMul(left, right).columns == right.columns
        // ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matMul(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
    {
        Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(right.columns, j requires 0 <= j < right.columns => Sum(seq(left.columns, k requires 0 <= k < left.columns => left.vals[i][k]*right.vals[k][j])))), left.rows, right.columns)
    }

    method parseInput(input: string) returns (orbits: seq<(string, string)>) 
    {
        var lines := splitOnBreak(input);
        orbits := Map((line) => var s:=split(line, ")"); assume {:axiom} |s| == 2; (s[0],s[1]), Filter(x => x != "", lines));
    }

    method countTransitive(start: (string, string), relation: set<(string, string)>, ghost visited: set<(string, string)>) returns (count: nat, children: set<(string, string)>) 
        decreases *
    {
        var next := set x | x in relation && start.1 == x.0;
        // assume visited !! next;
        var nextSeq := SetToSeq(next);
        var childCount: nat := 0;
        children := next;
        for i:=0 to |nextSeq| 
        {
            var cc, childs := countTransitive(nextSeq[i], relation, visited+{start,nextSeq[i]});
            print "\nCountTrans:";
            print "\n",nextSeq[i]," ", cc, " ", childs, "\n";
            children := children + childs;
            childCount := childCount + cc;
        }
        print "start: ", start, " ";
        print |children| + childCount, |children|, " ", childCount, " ", children, "\n";
        count := |next| + 2*childCount;
    }

    predicate rowHas(row: seq<int>) {
        exists i: nat :: i < |row| && row[i] != 0
    }

    predicate MatrixNotZero(m: Matrix) 
        requires isMatrix(m)
    {
        exists k: nat :: k < |m.vals| && rowHas(m.vals[k])
    }

    function SumConnections(m: Matrix): int
        requires isMatrix(m)
    {
        FoldLeft((sum, row)=> sum+ FoldLeft((a,b)=>a+b, 0, row), 0, m.vals)
    }

    method problem6_1(input: string) returns (x: int) 
        decreases *
    {
        var data := parseInput(input);
        var relation: set<(string, string)> := {};
        var index: nat := 0;
        var nodeIndex: map<nat, string> := map[];
        // var transitive 
        var nodes: set<string> :=  {};
        for i:=0 to |data|
        {
            // relation := relation+{data[i]}+(set x | x in relation && x.1 == data[i].0 :: (x.0, data[i].1));
            relation := relation+{data[i]};
            if data[i].0 !in nodes {
                nodeIndex := nodeIndex[index := data[i].0];
                index := index + 1;
            }

            if data[i].1 !in nodes {
                nodeIndex := nodeIndex[index := data[i].1];
                index := index + 1;
            }
            nodes := nodes + {data[i].1, data[i].0};

        }
        assume {:axiom} |nodes| > 0;
        assume {:axiom} forall i: nat :: i < |nodes| ==> i in nodeIndex.Keys;
        var rm := Matrice(seq(|nodes|, i requires 0 <= i < |nodes| => seq(|nodes|, j requires 0 <= j < |nodes| => if (nodeIndex[i], nodeIndex[j]) in relation then 1 else 0)), |nodes|, |nodes|);
        assert isMatrix(rm);
        // print rm;
        x := SumConnections(rm);
        var gm := matMul(rm, rm);

        var z :=0;
        while MatrixNotZero(gm)
            invariant isMatrix(gm)
            invariant gm.columns == rm.columns && gm.rows == rm.rows
            decreases *
        {
            print "\n";
            print z;
            // print gm;
            x := x + SumConnections(gm);
            gm := matMul(rm, gm);
            z := z + 1;
        }
        // assume {:axiom} exists ss :: ss in set x | x in relation && forall y :: y in relation && y != x ==> y.1 != x.0 ;
        // var start :| start in set x | x in relation && forall y :: y in relation && y != x ==> y.1 != x.0 ;
        // var count, cc := countTransitive(start, relation, {});
        return x;
    }

    method problem6_2(input: string) returns (x: int) {
        return 4;
    }
}
