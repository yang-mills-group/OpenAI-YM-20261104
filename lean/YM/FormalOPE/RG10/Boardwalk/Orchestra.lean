import YM.FormalOPE.RG10.Boardwalk.Flume
/-! # determinant/inverse at a polynomial-log leading

 *Scope*: `increases` may be as inverse determinant POLYNOMIAL in advertised Z (not only
 convergent limit to nonzero). Need this from geometry & chosen free basis/time.Price.Real.
 If comparing nearby leading det sequences at regulator & Gram inventory poly then derive it
 also on the perturbed procedure. Arithmetic on that reconstruction. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix Position.Grade Peal Trellis
open scoped Topology BigOperators Classical ContDiff
variable {I:Type*}{l:Filter I}{P:Path l}{r d n:ℕ}
structure Acr (P:Path l)(a:I→ℝ) : Prop where
 openAt : ∀ᶠ i in l, a i ≠ 0
 fee : Sized P (fun i=>(a i)⁻¹)
namespace Acr
variable {a b:I→ℝ}
variable (B:Acr P a)(h:Fair P a b)
local notation "u" => fun i=> (b i-a i) * (a i)⁻¹
include B h
lemma paid : Prize P (fun i=> (b i-a i) * (a i)⁻¹) := h.flip.shift.bilinear B.fee (ContinuousLinearMap.mul ℝ ℝ)
lemma flowing : ∀ᶠ i in l, b i≠0 := by
 have he := (paid B h).arrival.const_add 1; filter_upwards [he.eventually (isOpen_compl_singleton.mem_nhds (s:=({0}ᶜ:Set ℝ)) (show (1:ℝ)+0 ≠ 0 by norm_num)),B.openAt] with i hi hu
 intro k; apply hi; change 1+(b i-_)*_=0; rw [k,zero_sub, neg_mul, mul_inv_cancel₀ hu]; ring

lemma ready : Fair P (fun i=>(a i)⁻¹) (fun i=>(b i)⁻¹):= by
 have hx:Prize P u := paid B h
 let V:ℝ:=0; have he : Fair P u (fun _=>0):=⟨hx.size, hx.fit (Eventually.of_forall (fun _=> (sub_zero _).symm))⟩
 have hp:= (((Fair.fixed (1:ℝ)).join he).press (hasStrictFDerivAt_inv (𝕜:=ℝ) (x:=(1:ℝ)+0) (by norm_num)) (hx.arrival.const_add 1))
 apply (((Fair.same B.fee).mul hp).flip).fit (Eventually.of_forall (fun i=>by simp))
 filter_upwards [B.openAt,B.flowing h] with i hi hu;
 change _ *(1+(b i - a i) * _)⁻¹=(b i)⁻¹; field_simp; rw [add_sub_cancel _ _, div_self hu]

lemma rent : Acr P b:= ⟨B.flowing h,(B.ready h).rights⟩
omit B h
lemma source {K:ℝ} (hx:K ≠ 0)(hz:Tendsto a l (𝓝 K)): Acr P a:= ⟨hz.eventually (isOpen_compl_singleton.mem_nhds hx), Sized.income K⁻¹ (hz.inv₀ hx)⟩ -- mem_nhds resolves?
end Acr

namespace Posi
variable {a b : I→ fps}(H: Acr P (fun i=>constantCoeff (a i)))(h:Posi P r a b)
include h
lemma constants : Fair P (fun i=>constantCoeff (a i)) (fun i=>constantCoeff (b i)):= by simpa only [coeff_zero_eq_constantCoeff_apply] using! h 0 (Nat.zero_le _)
include H
lemma inverse' : Posi P r (fun i=>(a i)⁻¹) (fun i=>(b i)⁻¹):= by
 intro k hk; have hp:= H.ready h.constants
 induction k using Nat.strong_induction_on with
 | _ k ih=>
   simp_rw [PowerSeries.coeff_inv k]; split_ifs; exact hp
   apply hp.neg.mul; apply Fair.sum; intro i hi; have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi;
   split_ifs with hv; exact (h i.1 (by omega)).mul (ih i.2 hv (hv.le.trans hk)); exact Fair.fixed _
omit H h
lemma claim (x:fps): Ring.inverse x=x⁻¹:= by
 by_cases h:constantCoeff x=0;
 · rw [PowerSeries.inv_eq_zero.mpr h, Ring.inverse_non_unit x (by simp [PowerSeries.isUnit_iff_constantCoeff,h])]
 exact left_inv_eq_right_inv (Ring.inverse_mul_cancel x (by simpa [PowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero] using h)) (PowerSeries.mul_inv_cancel x h)
include H h
lemma rates : Posi P r (fun i=>Ring.inverse (a i)) (fun i=>Ring.inverse (b i)):= by simp_rw [claim]; exact h.inverse' H -- ordering inspect
end Posi
end YM.FormalOPE.RG10.Boardwalk
