/* Challenge 2 */

method Find (A : array<int>, K : int) returns (s : int , l : int)
  modifies A;
  requires 1 <= K <= A.Length;
  ensures 0 <= s < K <= l <= A.Length;
  ensures forall i, j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
  ensures forall i, j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
  ensures forall i, j :: s <= i <= j < l ==> A[i] == A[j];
{
  s, l := 0, A.Length; 
  //var done := false;
  var done := A.Length <= 1;
  var m, n := s, l;
  var w, X := s, A[K-1];
  while !done
    decreases !done;
    decreases l-s;
    invariant 0 <= s < K <= l <= A.Length;
    invariant forall i, j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
    invariant forall i, j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
    invariant done ==> forall i, j :: s <= i <= j < l ==> A[i] == A[j];
  {
    m, w, n, X := s, s, l, A[K-1];
    while w < n
      invariant s <= m <= w <= n <= l;
      invariant forall i :: s <= i < m ==> A[i] < X;
      invariant forall i :: m <= i < w ==> A[i] == X;
      invariant forall i :: n <= i < l ==> A[i] > X;
      invariant forall i, j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
      invariant forall i, j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
      invariant done ==> forall i, j :: s <= i <= j < l ==> A[i] == A[j];
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
    if n < K {
      s := n;
    } else if m < K <= n {
      s, l, done := m, n, true;
    } else {
      l := m;
    }
  }

}
