import YM.Integration.WilsonReceivedNominalRoot
import YM.Integration.WilsonCapturedPrimarySoftMount

/-! A signed countable collection of actual group words is received on the
chosen Wilson vacuum, including the values off each word's own chart. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPlantedGroupWords
open Function Finset RG Lattice Wilson Labels Source Ac Marker QuadraticLocal Push.Local Push.AbsoluteSums Push.Corrected
open Planned.GuardedAtom Extra.Histories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {A : Type} [Countable A] {d : ℕ} {F : Frame G d}

theorem mounted (P : Rep G n) (y : Site n) (T : A → Support n) (f : A → Config G n → ℂ)
    (roots : ∀a,y∈T a) (good : ∀a,P.p.Regular (T a) (f a))
    (e b : A→ℝ) (pos : ∀a,0≤e a) (gpos : ∀a,0≤b a)
    (caps : ∀a,P.p.supBounds y (T a) (f a) (e a)) (full : ∀a U,‖f a U‖≤b a)
    {E B : ℝ} (budget : SumBudget (fun a=>reservedMass P.p (T a) (e a)) E)
    (gross : SumBudget (fun a=>reservedMass P.p (T a) (b a)) B)
    (S : SectionData F) (Y : Hol G) (keeper : Guard.Keeper P.p P.activities)
    {σ c Λ δ η κ μ : ℝ} (law : P.Lawful σ c Λ δ η) (read : Readable Y S P.p n μ)
    (hp : 0<κ) (hη : 0≤η) (room : hitWidth P.p*η≤1) :
    Store P S Y y κ (cartage P.p Y S μ η κ (E+B) 0)
      (fun U=>(P.eval U:ℂ)*∑' a,f a U) := by
  let h a := f a-masked P.p.threshold (T a) (f a)
  let fee a:=e a+b a
  have adm : SumBudget (fun a=>reservedMass P.p (T a) (fee a)) (E+B) := by
    convert sumBudget_add budget gross using 1
    funext a; dsimp only [reservedMass,fee];ring
  have priced a : P.p.supBounds y (T a) (f a) (fee a) := by
    refine ⟨add_nonneg (pos a) (gpos a),fun U ok l ds bound=>((caps a).2 U ok l ds bound).trans ?_⟩
    exact le_add_of_nonneg_right (gpos _)
  have attaches a : Attaches P.p.threshold (T a) (h a) := by
    let g:=good a
    exact ⟨fun U W same flags=>congrArg₂ (·-·) (g.sites U W same) (uses_mask _ g.sites U W same flags),
      fun k U=>congrArg₂ (·-·) (g.symmetry k U) (invariant_mask g.symmetry _ _ k U),
      g.borel.sub (masked_measurable _ _ _ g.borel),fun U ok=>sub_eq_zero.mpr (masked_eq _ _ _ _ ok).symm⟩
  have hull a U : ‖h a U‖ ≤ b a := by
    by_cases p:Healthy P.p.threshold (T a) U
    · simp only [h,Pi.sub_apply,masked_eq _ _ _ _ p,sub_self,norm_zero];exact gpos _
    · simpa only [h,Pi.sub_apply,masked_ne _ _ _ _ p,sub_zero] using full a U
  have width : 0 ≤ P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  have summable : Summable b:=gross.2.1.of_nonneg_of_le gpos fun a=>le_mul_of_one_le_left (gpos _)
    (Real.one_le_exp (mul_nonneg width (Nat.cast_nonneg _)))
  have ms (U:Config G n): Summable (fun a=>masked P.p.threshold (T a) (f a) U) := by
    apply Summable.of_norm_bounded summable
    intro a
    by_cases p:Healthy P.p.threshold (T a) U
    · rw [masked_eq _ _ _ _ p];exact full a U
    · rw [masked_ne _ _ _ _ p,norm_zero];exact gpos _
  have hs (U:Config G n) : Summable (fun a=>h a U):=Summable.of_norm_bounded summable (fun a=>hull a U)
  have blank : ForceFormat P.p P.activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have quiet : ForceCost P.p P.activities 0 (κ*0) := by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  obtain ⟨q,shape,charged,data,-⟩:=WilsonCenteredMountedCapture.original y T
    (docket A) keeper (docket (A×Finset ℕ)) 0 f h 0 S Y law read hp hη room roots good
    fee adm priced attaches (fun a U=>(hull a U).trans (le_add_of_nonneg_left (pos a))) blank quiet ms hs
  refine ⟨q,shape,charged.bound le_rfl,fun U=>?_⟩
  have same a : masked P.p.threshold (T a) (f a) U+h a U=f a U := by dsimp only [h,Pi.sub_apply];abel
  rw [data];simp_rw [same];simp

end YM.Integration.WilsonPlantedGroupWords
