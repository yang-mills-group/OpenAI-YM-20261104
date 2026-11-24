import YM.Comparison.RG02.Assembly.Radial
import YM.Comparison.RG02.Order.Pay
/-!
# Auditing the first anticipated interaction

 Reading at grade zero/one in the declared g. Includes countermass and marked quotients,
 even allowing general (non-singleton, nonzero leading) marker drivers. Only at the prescribed
 order; does not gather virtual/local costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order.First
open Function Filter Finset MeasureTheory
open Marker Multi PertExtension.Series
open YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
local notation "B"=>Board R r
abbrev buc (x : Grade R r) := observe R r x 0
abbrev ind (x : Grade R r) := observe R r x 1

variable (h : 0<r) {x y : Grade R r} (hx : Symmetric x) (hy : Symmetric y)
local notation "ℙ"=>Marker.Poly R
include hx hy
lemma buc_mul : buc (x*y)=buc x*buc y:= by
   obtain ⟨p,h⟩:=hx; obtain ⟨q,hq⟩:=hy; unfold buc; rw [← h,← hq,← map_mul,observation _ _ _ (Nat.zero_le _),observation _ _ _ (Nat.zero_le _),observation _ _ _ (Nat.zero_le _)]; simp
include h in
lemma ind_mul : ind (x*y)=ind x*buc y+buc x*ind y:= by
   obtain ⟨p,hp⟩:=hx; obtain ⟨q,hq⟩:=hy; unfold buc ind; rw [← hp,← hq,← map_mul]; simp_rw [observation _ _ _ (show 1≤r from h), observation _ _ _ (Nat.zero_le _)]; rw [PowerSeries.coeff_one_mul,PowerSeries.coeff_zero_eq_constantCoeff]; congr 1; exact mul_comm _ _
omit hy
omit hx
lemma buc_one : buc (1 : Grade R r)=(1:ℙ) := by rw [← map_one (series R r), buc, observation _ _ _ (Nat.zero_le _)]; simp
lemma ind_one : ind (1: Grade R r)=(0:ℙ) := by
   by_cases H : 1≤r
   · rw [← map_one (series R r),ind,observation _ _ _ H]; simp
   exact dif_neg H -- check if not dif
include hx
lemma buc_pow (n : ℕ): buc (x^n)=buc x ^ n:= by
  induction n with
  | zero=> rw [pow_zero,pow_zero,buc_one]
  | succ n ih=> rw [pow_succ,pow_succ,buc_mul (hx.pow n) hx,ih] -- pow_succ rewrite maybe
include h in
lemma ind_pow (n : ℕ): ind (x^(n+1))=((↑(n+1):ℂ)) • (ind x * (buc x)^n) := by
   induction n with
   | zero=> simp
   | succ n ih=> rw [pow_succ _ (n+1),ind_mul h (hx.pow _) hx, ih, buc_pow hx, smul_mul_assoc, mul_comm (buc x ^ _)]; push_cast; rw [add_smul,one_smul, pow_succ (buc x) n]; simp only [mul_assoc, add_smul,one_smul]; -- inspect

variable (he : x.part (Board R r).quiet=0) (x' : Grade R r)
omit hx in
lemma buc_vac : (buc x').part R.quiet=x'.part (B).quiet := by unfold buc; have he:= observed (x:=x') R.quiet (Nat.zero_le r); rw [show pick r 0=(indices r).quiet from Subtype.ext (Finset.card_eq_zero.mp (picked r (Nat.zero_le _))),Join.pair_quiet] at he; simpa using he
include he
private def no_more (r : ℕ) (V : Type)[Fintype V]:= Fintype.card (V⊕ Fin r)
local notation "n"=> Fintype.card (V⊕ Fin r)
lemma buc_pass : buc (Poly.pass x) = Poly.pass (buc x) := by
   change observeL 0 (Poly.pass x)= _; unfold Poly.pass; rw [map_sum]; simp_rw [map_smul]
   trans ∑ i∈range (n+1), (i.factorial:ℂ)⁻¹ • (buc x)^i
   · exact Finset.sum_congr rfl fun k _=> by rw [←buc_pow hx]; rfl
   symm; exact pass_extended _ ((buc_vac _).trans he) (by simp)
include h in
lemma ind_pass : ind (Poly.pass x)= ind x * Poly.pass (buc x) := by
   change observeL 1 (Poly.pass x)= _; rw [Poly.pass, map_sum, Finset.sum_range_succ',pass_extended (buc x) ((buc_vac x).trans he) (show Fintype.card V≤n from by simp), Finset.mul_sum,Finset.sum_range_succ _ n]
   rw [pow_zero, show observeL 1 ((Nat.factorial 0:ℂ)⁻¹ • (1:Grade R r))=0 by simp only [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]; exact ind_one,
     Poly.stops (buc x) ((buc_vac x).trans he) _ (show Fintype.card V<n from by simpa using h), smul_zero, mul_zero,add_zero,add_zero]
   refine sum_congr rfl (fun i _=>?_); rw [map_smul]; change _ • ind _=_
   rw [ind_pow h hx,mul_smul_comm, smul_smul, Nat.factorial_succ,Nat.cast_mul,mul_inv_rev,mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)),mul_one]

omit he
-- quotient formula. at(r)>=1. wants colors sparse.
variable (hh : UnitLeading x)
include hh
omit hx in
private lemma leading_mass : buc (denominator x)=1 := by rw [buc,denominator,observe_bottom]; change Poly.send R.quiet ((observe R r x 0).part R.quiet)=_; rw [show (observe R r x 0).part R.quiet=1 from (buc_vac x).trans hh]; rfl
lemma buc_ratio : buc (Order.ratio x)= buc x := Eq.trans (one_mul _).symm (Eq.trans (congrArg (· * _) ((leading_mass hh).symm)) ((buc_mul (show Symmetric (denominator x) from hx.vacant) (sym_ratio hh hx)).symm.trans (congrArg buc (recovers hh))))
include h in
lemma ind_ratio : ind (Order.ratio x)=ind x - ind (denominator x)*buc x := by
   apply eq_sub_of_add_eq; have ht:= ind_mul h (show Symmetric (denominator x) from hx.vacant) (sym_ratio hh hx); rw [buc_ratio hx hh,leading_mass hh,recovers hh,one_mul] at ht; rw [ht,add_comm] -- recursion?
include h in
lemma ind_connected : ind (connected x)=ind x * inverseMass (buc x) := by
   have hp:= ind_pass h (hx.log hh) (connected_quiet hh)
   have he := buc_pass (hx.log hh) (connected_quiet hh)
   rw [pass_connected hh] at he hp; rw [← he] at hp
   rw [hp, mul_assoc,right_inverse ((buc_vac x).trans hh),mul_one]
include h in
lemma first_log : ind (Order.logMarked x)= (ind x * inverseMass (buc x)) - Poly.bead R ((ind x).part R.quiet) := by
   have ht:= ind_connected h (sym_ratio hh hx) (ratio_quiet hh)
   unfold logMarked; rw [ht,buc_ratio hx hh, ind_ratio h hx hh,sub_mul,mul_assoc,right_inverse ((buc_vac x).trans hh),mul_one]; congr 1; exact observe_bottom x _
end YM.Comparison.RG02.Order.First
