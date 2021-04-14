# Group Identification

- Filipe Marques, 86411, filipe.s.marques@tecnico.ulisboa.pt

# Implemented Features

Using the **Evaluation components** we identify the implemented and missing
features of our specification.

## Challenge 1: Partitioning an Array

* The algorithm affects only the specified segment of array: **YES**
* The algorithm does not change elements outside the considered segment : **YES**
* The algorithm does not remove existing elements nor add new elements: **YES**
* The algorithm creates the three regions as specified: **YES**
* The algorithm terminates: **YES**

## Challenge 2: Finding the K Smallest Element

* The algorithm places the *K* smallest elements in the first *K* positions: **YES**
* The $K^{th}$ smallest element is identified: **YES**
* The algorithm does not remove existing elements nor add new elements: **YES**
* The algorithm terminates: **NO**
  * The verified implementation developed by Roland Backhouse, which we 
    implemented, terminates. However, when using the bound function
    specified in the paper, Dafny is unable to prove termination.
  * In the bullet below we discuss why this might happen.
* When reusing the solution to Challenge 1, new annotations might have to be 
  introduced: **YES**
  * The following pre-conditions were added in `Partition`:
    * `requires 0 <  s <= l <= A.Length ==> inplace(A, 0, s, A.Length);`
    * `requires 0 <= s <= l <  A.Length ==> inplace(A, 0, l, A.Length);`
  * The following post-conditions were added in `Partition`:
    * `ensures 0 <  s <= l <= A.Length ==> inplace(A, 0, s, A.Length);`
    * `ensures 0 <= s <= l <  A.Length ==> inplace(A, 0, l, A.Length);`
  * These ensure the post-conditions in `Find` are maintained.
  * Further annotations that help prove progress of the main loop 
    in `Find` might be missing and that's why we can't prove termination
    in the point above.
    * We tried specifying post-conditions for properties that `Partition` 
      ensures on the retuned values of `m` and `n`, but these efforts
      were obviously unsuccessful.

## Challenge 3: A CLI Selection Utility

* The program show appropriate error messages: **MEH**
  * Almost all unintended behaviour is documented:
    * Unspecified behaviour with negative integers
* The program only writes to the destination file if there isn't already a 
  file with the name provided: **YES**
  * Instead of this exact condition what we did was:
    * If a file with the specified name exist we exit immediately 
* The stream that is written to the destination file satisfies the required 
  conditions: **MEH**
  * We interpreted this as:
    * The find algorithm must run on a valid array and return an array 
      that satisfies the algorithms post-conditions.
    * We write the resulting array's data to the output file in the 
      appropriate format.
  * We did not verify if data is added or removed from the initial input 
    stream to the generated output stream, as verifying these properties
    in the I/O helpers was to difficult.
