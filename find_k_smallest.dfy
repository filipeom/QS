/*  
 * This is the skeleton for the CLI program (Challenge 3).
 * 
 * You can compile this program by running the command:
 *
 *       dafny find_k_smallest.dfy Io.dfy IoNative.cs
 */

include "Io.dfy"

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
{
  print "TODO!\n";  
}
