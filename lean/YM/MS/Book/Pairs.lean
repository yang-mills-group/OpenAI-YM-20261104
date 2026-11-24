import Mathlib.Algebra.BigOperators.NatAntidiagonal

namespace YM.MS.Book.Convolve
open Finset

abbrev T (X:Type*):= ℕ→X
variable {Y : Type*} [AddCommMonoid Y]
lemma associate (F:ℕ→ℕ→ℕ→Y) (n:ℕ) : ∑ i∈antidiagonal n,∑ j∈antidiagonal i.2,F i.1 j.1 j.2=∑ i∈antidiagonal n,∑ j∈antidiagonal i.1, F j.1 j.2 i.2:= by
    -- induction n first index. covers 0.., first+ recursive.
    induction n generalizing F with
    | zero=> simp
    | succ n ih=>
       rw [Finset.Nat.sum_antidiagonal_succ,Finset.Nat.sum_antidiagonal_succ]; simp_rw [Finset.Nat.sum_antidiagonal_succ]; -- inspect
       rw [ih (fun i j=> F (i+1) j),Finset.sum_add_distrib]; simp [add_assoc]
end YM.MS.Book.Convolve
