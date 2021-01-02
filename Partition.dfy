/* Challenge 1 */

method Partition (A : array<int>, s : int, l : int, X : int) returns (m : int, n : int)
  modifies A
  requires 0 <= s <= l <= A.Length
  /* Ensures *m* and *n* are inside the segment */
  ensures s <= m <= n <= l
  ensures forall i :: s <= i < m ==> A[i] < X
  ensures forall i :: m <= i < n ==> A[i] == X
  ensures forall i :: n <= i < l ==> A[i] > X
  /* All the other elements should be left unchanged */
  ensures (A[..s] == old(A[..s])) && (A[l..] == old(A[l..]))
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  var w := s;
  m, n := s, l;
  while w < n
    invariant s <= m <= w <= n <= l
    invariant forall i :: s <= i < m ==> A[i] < X
    invariant forall i :: m <= i < w ==> A[i] == X
    invariant forall i :: n <= i < l ==> A[i] > X
    invariant forall i :: 0 <= i < s ==> A[i] == old(A[i])
    invariant forall i :: l <= i < A.Length ==> A[i] == old(A[i])
    invariant multiset(A[..]) == multiset(old(A[..]))
  {
    if A[w] < X {
      A[m], A[w] := A[w], A[m];
      m, w := m + 1, w + 1;
    } else if A[w] == X {
      w := w + 1;
    } else {
      A[n-1], A[w] := A[w], A[n-1];
      n := n - 1;
    }
  }
}
