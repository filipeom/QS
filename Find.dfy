/* Challenge 2 */

include "Partition.dfy"

method Find(A : array<int>, K : int) returns (s : int , l : int)
  requires A.Length > 0;
  requires 1 <= K <= A.Length;
  modifies A;
  ensures 0 <= s < K <= l <= A.Length;
  ensures forall i,j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
  ensures forall i,j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
  ensures forall i,j :: s <= i <= j < l ==> A[i] == A[j];
  ensures multiset(A[..]) == multiset(old(A[..]))
  ensures A[s] == A[K-1];
{
  s, l := 0, A.Length;
  var done := false;
  while !done
    invariant 0 <= s < K <= l <= A.Length
    invariant forall i,j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
    invariant forall i,j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
    invariant done ==> forall i,j :: s <= i <= j < l ==> A[i] == A[j];
    invariant multiset(A[..]) == multiset(old(A[..]))

    decreases !done, l - s;
  {
    var X := A[K-1];
    var m, n := Partition(A, s, l, X);
    if n < K {
      s := n;
    } else if m < K <= n {
      s, l, done := m, n, true;
    } else if K <= m {
      l := m;
    }
  }
}
