import YM.Integration.WilsonAllDateHarvestLedger

/-! Comparison of genuine MenuBoard witnesses on the same singleton rows. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonAllDateHarvestStability

open Function Finset MeasureTheory Lattice Wilson RG MergeProof MergeProof.Accent
open Marker RG05Readout RG05Readout.Address RG05Readout.Many
open Extra.Histories Push Ac GridApprox.Nil
open WilsonAllDateHarvestAffine WilsonAllDateHarvestLedger
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {J:Census V}
variable {G:Gauge} {n:Side} {P:Rep G n} {rows:V→Address.Three G n}
variable {o:V→Site n} {w:V→ℝ} {α:ℝ} {X Y:Config G n→Poly J}

/-- All represented quantities on the same genuine coarse singleton bank. -/
structure Ledger (P:Rep G n) (rows:V→Address.Three G n) (X:Config G n→Poly J)
    (o:V→Site n) (w:V→ℝ) (α:ℝ) where
  H : Support n→ Config G n→Poly J
  K : Box n→ Config G n→Poly J
  legal : Carton o H K P.p.threshold
  regular : Towed w id H P.p.B α 1
  forced : Towed w Prod.fst K P.p.B α 1
  paid : X=restore P (fun j=>(rows j).2.1) (fun j=>profile P.activities (rows j).2.2) H K

variable {I Y' : Type*} {S:I→Support n} {F H:I→Y'→Poly J} {B:ℕ}

omit [Fintype V] in
private theorem interpolate (hF:Towed w S F B α 1) (hH:Towed w S H B α 1)
    (t:ℝ) (ht:0≤t) (hu:t≤1) :
    Towed w S (fun s U=>blend (F s U) (H s U) (t:ℂ)) B α 1 ∧
    Towed w S (fun s U=>blend (F s U) (H s U) (t:ℂ) - F s U) B α (2*t) := by
  have nt : ‖(t:ℂ)‖=t := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  have ns : ‖(1:ℂ)-t‖=1-t := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hu)]
  constructor
  · have h:=towed hF hH (1-(t:ℂ)) (t:ℂ)
    rw [ns,nt,mul_one,mul_one,sub_add_cancel] at h
    simpa only [blend_eq] using h
  have h:=towed hF hH (-(t:ℂ)) (t:ℂ)
  rw [norm_neg,nt,mul_one,←two_mul] at h
  have point (x y:Poly J) : blend x y (t:ℂ)-x = linear (-(t:ℂ)) (t:ℂ) x y := by
    unfold blend linear
    rw [smul_sub,neg_smul]
    abel
  simpa only [point] using h

/-- Both original expenditures of the actual interpolated output are one. The
difference to the stripped output costs at most twice the input fraction. -/
theorem output (cap:WilsonAllDateHarvestAffine.Three J)
    (base:MenuBoard P rows X o w α 1) (upper:MenuBoard P rows Y o w α 1)
    (t:ℝ) (ht:0≤t) (hu:t≤1) :
    ∃ (A:Ledger P rows X o w α)
      (C:Ledger P rows (fun U=>blend (X U) (Y U) (t:ℂ)) o w α),
      Towed w id (fun s U=>C.H s U - A.H s U) P.p.B α (2*t) ∧
      Towed w Prod.fst (fun s U=>C.K s U - A.K s U) P.p.B α (2*t) := by
  obtain ⟨H,K,ca,fp,kp,ex⟩:=base.grants
  obtain ⟨H',K',cb,fq,kq,ey⟩:=upper.grants
  obtain ⟨hc,hd⟩:=interpolate fp fq t ht hu
  obtain ⟨kc,kd⟩:=interpolate kp kq t ht hu
  have legal:=carton ca cb (1-(t:ℂ)) (t:ℂ)
  simp only [←blend_eq] at legal
  refine ⟨⟨H,K,ca,fp,kp,ex⟩,⟨_,_,legal,hc,kc,?_⟩,hd,kd⟩
  funext U
  rw [ex,ey]
  exact (original _ _ _ cap (fun i=>(ca.exp i).2) (fun i=>(cb.exp i).2)
    (fun i=>(ca.flag i).2) (fun i=>(cb.flag i).2) (t:ℂ) U).symm

end YM.Integration.WilsonAllDateHarvestStability
