/* Challenge 2 */

//include "Partition.dfy"

// TODO: Another predicate for well no change in arr

predicate inplace(a : array<int>, l : int, m : int, u : int)
  requires 0 <= l <= m <= u <= a.Length;
  reads a;
{
  forall i,j :: l <= i < m <= j < u ==> a[i] < a[j]
}

method Swap(a : array<int>, k : int, k' : int)
  requires a.Length > 0;
  requires 0 <= k < a.Length;
  requires 0 <= k' < a.Length;
  modifies a;
  ensures a[k] == old(a[k']);
  ensures a[k'] == old(a[k]);
  ensures forall i :: 0 <= i < a.Length && i !in {k, k'} ==> a[i] == old(a[i])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  a[k], a[k'] := a[k'], a[k];
}

method Partition(A : array<int>, s : int, l : int, X : int) returns (m : int, n : int)
  requires A.Length > 0;
  requires s <= l;
  requires 0 <= s <= l <= A.Length;
  requires 0 < s <= l <= A.Length ==> inplace(A, 0, s, A.Length);
  requires 0 <= s <= l < A.Length ==> inplace(A, 0, l, A.Length);

  modifies A;

  /* Expected behaviour */
  ensures 0 <= s <= m <= n <= l <= A.Length
  ensures forall i :: s <= i < m ==> A[i] < X;
  ensures forall i :: m <= i < n ==> A[i] == X;
  ensures forall i :: n <= i < l ==> A[i] > X;
  /* No unexpected changes occured */
  ensures s > 0 ==> forall i :: 0 <= i < s ==> A[i] == old(A[i]);
  ensures l < A.Length ==> forall i :: l <= i < A.Length ==> A[i] == old(A[i]);
  ensures multiset(A[..]) == multiset(old(A[..]));
  /* Assure partitioning is maintained */
  ensures 0 < s <= l <= A.Length ==> inplace(A, 0, s, A.Length);
  ensures 0 <= s <= l < A.Length ==> inplace(A, 0, l, A.Length);

{
  var k := s;
  m, n := s, l;
  while k < n
    invariant 0 <= s <= m <= k <= n <= l <= A.Length;
    invariant forall i :: s <= i < m ==> A[i] < X;
    invariant forall i :: m <= i < k ==> A[i] == X;
    invariant forall i :: n <= i < l ==> A[i] > X;
    invariant s > 0 ==> forall i :: 0 <= i < s ==> A[i] == old(A[i]);
    invariant l < A.Length ==> forall i :: l <= i < A.Length ==> A[i] == old(A[i]);
    invariant 0 < s <= l <= A.Length ==> inplace(A, 0, s, A.Length);
    invariant 0 <= s <= l < A.Length ==> inplace(A, 0, l, A.Length);
    invariant multiset(A[..]) == multiset(old(A[..]));

    decreases n - k;
  {

    if A[k] < X {
      Swap(A, m, k);
      m := m + 1;
      k := k + 1;
    } else if A[k] == X {
      k := k + 1;
    } else if A[k] > X {
      Swap(A, n-1, k);
      n := n - 1;
    }
  }
}

method Find(A : array<int>, K : int) returns (s : int , l : int)
  requires A.Length > 0;
  requires 1 <= K <= A.Length;
  modifies A;
  ensures 0 <= s < K <= l <= A.Length;
  ensures forall i,j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
  ensures forall i,j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
  ensures forall i,j :: s <= i <= j < l ==> A[i] == A[j];
  ensures A[s] == A[K-1];
{
  s, l := 0, A.Length;
  var done := false;
  while !done
    invariant 0 <= s < K <= l <= A.Length
    invariant forall i,j :: 0 <= i < s <= j < A.Length ==> A[i] < A[j];
    invariant forall i,j :: 0 <= i < l <= j < A.Length ==> A[i] < A[j];
    invariant done ==> forall i,j :: s <= i <= j < l ==> A[i] == A[j];

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
