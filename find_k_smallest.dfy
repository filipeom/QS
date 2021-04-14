/*  
 * This is the skeleton for the CLI program (Challenge 3).
 * 
 * You can compile this program by running the command:
 *
 *       dafny find_k_smallest.dfy Io.dfy IoNative.cs
 */

include "Io.dfy"
include "Find.dfy"

function method power(b:int, e:nat):int
{
	if (e==0) then 1 else b * power(b,e-1)
}

method atoi(s : seq<char>) returns (n : int)
  requires |s| > 0;
{
  n := 0;
  var i := |s| - 1;
  while i >= 0 {
    n := n + power(10, |s| - i - 1) * ((s[i] as int) - 48);
    i := i - 1;
  }
}

method itoa(n : int) returns (s : seq<char>)
  ensures forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9');
{
  var n', i, len;

  /* if n' is >= 0 proving termination is trivial */
  if (n < 0) { 
    n' := -n;
  } else {
    n' := n;
  }
  /* find str len */
  len := 0;
  while n' != 0 
    invariant n' >= 0;
  {
    n' := n' / 10;
    len := len + 1;
  }

  /* allocate space for string */
  var a := new char[len];

  /* convert int into string */
  n', i := n, 0;
  while i < len
    invariant 0 <= i <= len;
    invariant forall k :: 0 <= k < i <= len ==> ('0' <= a[k] <= '9');
  {
    a[i] := (n'%10 + 48) as char;
    n' := n' / 10;
    i := i + 1;
  }

  /* reverse string */
  i := 0;
  while i < len/2 
    invariant 0 <= i <= len/2;
    invariant forall k :: 0 <= k < len ==> ('0' <= a[k] <= '9');
  { 
    var j := len - i - 1;
    a[i], a[j] := a[j], a[i];
    i := i + 1;
  }
  s := a[..];
  assert forall i :: 0 <= i < len ==> ('0' <= s[i] <= '9');
}

method get_line(b : array<byte>, o : int) returns (k : int, s : seq<char>)
  requires b.Length > 0;
  requires 0 <= o < b.Length
  ensures 0 <= o < k <= b.Length;
{
  s := [];
  k := o;
  while k < b.Length && b[k] != 0x0A
    invariant 0 <= o <= k <= b.Length;
    invariant k-o == |s|;
    invariant |s| >= 0;
    decreases b.Length - k;
  {
    s := s + [b[k] as char];
    k := k + 1;
  }
  /* if we can, move index to start of newline */
  if k < b.Length {
    k := k + 1;
  }
}

method deserialize_array(b : array<byte>)
    returns (a' : array<int>)
  requires b.Length > 0;
  ensures fresh(a')
{
  var a;
  var i, line;

  /* parse array into seq a */
  i := 0;
  while i < b.Length 
    invariant 0 <= i <= b.Length;
    decreases b.Length-i;
  {
    i, line := get_line(b, i);
    /* ignore empty lines */
    if |line| > 0 {
      var n := atoi(line);
      a := a + [n];
    }
  }
  /* create output array */
  a' := new int[|a|];
  /* cpy seq a into output array a'*/
  i := 0; 
  while i < |a| {
    a'[i] := a[i];
    i := i + 1;
  }
}

method serialize_array(a : array<int>, b : array<byte>)
  requires a.Length > 0 && b.Length > 0;
  modifies b;
{
  var len, s;
  var ai, bi, si;

  ai, bi, len := 0, 0, a.Length;
  while (ai < len) && (bi < b.Length)
    invariant 0 <= ai <= a.Length;
    invariant 0 <= bi <= b.Length;
  {
    /* get string repr of int */
    s := itoa(a[ai]);
    /* write to b as a byte */
    si := 0;
    while (si < |s|) && (bi < b.Length)
      invariant 0 <= si <= |s|;
      invariant 0 <= bi <=  b.Length;
    {
      b[bi] := s[si] as byte; 
      bi, si := bi + 1, si + 1;
    }
    /* newline */
    if (bi < b.Length) {
      b[bi] := 0x0A;
      bi := bi + 1;
    }
    ai := ai + 1;
  }
}

method find_k_smallest(ghost env:HostEnvironment, K : array<char>, src_path : array<char>, 
src : FileStream, dst : FileStream) returns (success : bool, A : array?<int>)
  requires env.Valid() && env.ok.ok();
  requires K.Length > 0;
  requires src_path[..] == src.Name();
  requires src.Name() in env.files.state() && dst.Name() in env.files.state();
  requires env == src.env == dst.env;
  requires env.ok == src.env.ok == dst.env.ok
  requires env.files == src.env.files == dst.env.files
  requires src.IsOpen() && dst.IsOpen();
  requires src != dst;
  requires env.files.state()[dst.Name()] == [];
  modifies env, env.files, env.ok, src, dst, src.env, src.env.ok, src.env.files;
  ensures A != null ==> env.ok != null && env.ok.ok() == true && A.Length > 0;
  ensures success ==> A != null && A.Length > 0;
{
  var ok, len := FileStream.FileLength(src_path, env);
  if !ok {
    print "[Err] Unable to find length of src.\n";
    return false, null;
  }

  if len <= 1 {
    print "[Err] File to small\n";
    return false, null;
  }

  var b := new byte[len];
  ok := src.Read(0, b, 0, len);
  if !ok {
    print "[Err] Unable to read data from src.\n";
    return false, null;
  }
  assert b[..] == old(env.files.state()[src_path[..]]);

  A := deserialize_array(b);
  if A.Length == 0 {
    print "[Err] Unable to parse array.\n";
    return false, null;
  }

  var K' := atoi(K[..]);
  if K' < 1 || K' > A.Length {
    print "[Err] Invalid K value.\n";
    return false, null;
  }

  var s, l := Find(A, K');
  serialize_array(A, b);

  ok := dst.Write(0, b, 0, len);
  if !ok {
    print "[Err] Unable to write into dst file.\n";
    return false, null;
  }
  assert b[..] == env.files.state()[dst.Name()];

  ok := src.Close();
  if !ok {
    print "Failed to close the src file: ", src, "\n";
    return false, null;
  }
	
  ok := dst.Close();
  if !ok {
    print "Failed to close the dst file: ", dst, "\n";
    return false, null;
  }
 
  return true, A;
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env, env.files, env.ok;
{
  var arg_num := HostConstants.NumCommandLineArgs(env);
  if arg_num < 4 {
    print "Usage: find_k_smallest.exe K <src_path> <dst_path>\n";
    return;
  }
  
  var K        := HostConstants.GetCommandLineArg(1, env);
  var src_path := HostConstants.GetCommandLineArg(2, env);
  var dst_path := HostConstants.GetCommandLineArg(3, env);

  if K.Length <= 0 {
    print "[Err] Invalid K value.\n";
    return;
  }

  var src_exists := FileStream.FileExists(src_path, env);
  if !src_exists {
    print "[Err] src file \"", src_path, "\" not found.\n";
    return;
  }

  var dst_exists := FileStream.FileExists(dst_path, env);
  if dst_exists {
    print "[Err] dst file \"", dst_path, "\" in use.\n";
    return;
  }

  var ok, src_stream := FileStream.Open(src_path, env);
  if !ok {
    print "[Err] Unable to open src file.\n";
    return;
  }

  var dst_stream;
  ok, dst_stream := FileStream.Open(dst_path, env);
  if !ok {
    print "[Err] Unable to open dst file.\n";
    return;
  }

  var A;
  ok, A := find_k_smallest(env, K, src_path, src_stream, dst_stream);
}
