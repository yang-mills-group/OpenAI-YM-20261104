import YM.Integration.WilsonMeasuredOriginalPeriodWord
import YM.Integration.WilsonMeasuredOriginalCatalogueUnion

/-! The real copied fields agree on the finite group word without another income assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredUnconditionalCatalogue
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 FVA1Physical.TwoReset
open AnalyticBridge.SectorAffine.Offset WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {C V X:Type} [Fintype C] [Fintype V]
  {I:C→Type} {K:V→Type} {P:C→Passport n Unit} {S:V→Passport n Unit}
  {J:Census Unit} {D:ℕ}
variable (F:(z:C)→I z→Row (P z) J G X) (T:(v:V)→K v→Row (S v) J G X)


variable (d:ℕ) (s:Multi.Hot J) (t:X)
local notation "code" => (fun _:Unit=>d)
local notation "model" => rows (D:=D) F T
variable (r:ℝ) (c:V→ℕ→ℝ)
variable (L:Layout G) (tape:Finset Age)
local notation "pole₀" => Launch.index J code s.val + 1

theorem angular
    (read:∀e≤D,∀B:Stationary.Link G n,
      (r:ℂ)*(∑z,(peek dvd_rfl (F z) code L tape t e B).part s.val) =
        ∑v,∑l∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
          (c v l.1:ℂ)*(peek dvd_rfl (T v) code L tape t l.2 B).part s.val)
    (i:ℕ) (hi:i < pole₀ + D + 1) (u:Directions G n) :
    (∑a:Names C V D,weight r c a • WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i u a)=0 := by
  let A:=WilsonCubicOriginalTorus.coordinates G n u
  let top (z:C)(j:ℕ):=(peek dvd_rfl (F z) code L tape t j A).part s.val
  let bottom (v:V)(j:ℕ):=(peek dvd_rfl (T v) code L tape t j A).part s.val
  have identical(a:Names C V D):WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i u a =
      slice pole₀ i (lag a) (WilsonMeasuredTransitionCatalogue.value top bottom a) := by
    cases a with
    | inl z =>
      unfold WilsonEmittedFiledGerm.price slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,top]
      split
      · rw [WilsonMeasuredOriginalPeriodWord.literal (F z) code L tape t _ A]
        rfl
      · rfl
    | inr b =>
      rcases b with ⟨v,l⟩
      unfold WilsonEmittedFiledGerm.price slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,bottom]
      split
      · rw [WilsonMeasuredOriginalPeriodWord.literal (T v) code L tape t _ A]
        rfl
      · rfl
  simp_rw [identical]
  exact WilsonMeasuredTransitionCatalogue.signed r c top bottom (fun e he=>read e he A) pole₀ i hi

end YM.Integration.WilsonMeasuredUnconditionalCatalogue
end
