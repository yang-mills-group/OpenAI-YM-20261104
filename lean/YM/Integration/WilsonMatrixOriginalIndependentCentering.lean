import YM.Integration.WilsonMatrixOriginalIndependentUnit
import YM.Integration.WilsonReportingPrescribedOldAction

/-! The lower glyph disappears from connected finite reads on both the corrected and independent sides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentCentering
open Lattice Wilson RG Precision Source MS.Local.Physical MS.Menus MS.Theater MS.Land
open FVA2 FVA2.Warehouse PhysicalNext.Repeat.Legato MeasureTheory Finset
open WilsonMatrixOriginalIndependentFields WilsonMatrixTicketLanesNativePrices
open ActualOriginalDictionary
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G)

def tag (i:Glyph B 4):MS.Rake.Label B:=⟨i.1.val,i.2⟩

private theorem null_grade {h s:ℕ} (z:B.BIndex (h:ℤ) s) (zero:s=0)
    (n:Side) (o:Site n) (U V:Config G n):
    ((dictionary R B).cylinder h s z).O n o U = ((dictionary R B).cylinder h s z).O n o V :=by
  subst s
  exact WilsonReportingPrescribedOldAction.flat R B h z n o U V

/-- The complete original calibrated coefficient, with every original order and fee, is constant. -/
theorem nominal (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4)
    (Q:Prescription B) (μ:ℝ) (k:ℕ) (n:Side) (o:Site n) (U V:Config G n):
    ActualOriginalCalibratedColumns.weightedObservable R B Q (tag B i) μ n o U k =
      ActualOriginalCalibratedColumns.weightedObservable R B Q (tag B i) μ n o V k:=by
  have h0:i.1.val=0:=congrArg Prod.fst (WilsonMatrixOriginalIndependentUnit.degree B (warehouse R) simple i low)
  let u:=tag B i
  have expansion (A:Config G n):ActualOriginalCalibratedColumns.weightedObservable R B Q u μ n o A k =
      ∑ g:Glyph B u.h,oil (Q.fees u.h u.item) g k μ * (((dictionary R B).cylinder g.size g.grade g.2.2).O n o A:ℂ):=by
    unfold ActualOriginalCalibratedColumns.weightedObservable WilsonComparison.Finite.Dictionary.calibrated
    rw [List.map_map,←Multiset.sum_coe,←Multiset.map_coe,Finset.coe_toList,←Finset.sum]
    rfl
  change ActualOriginalCalibratedColumns.weightedObservable R B Q u μ n o U k=_
  rw [expansion U,expansion V]
  apply sum_congr rfl
  intro g _
  have a:(g.1.val)<u.h+1:=g.1.isLt
  have b:g.2.1.val<g.1.val+1:=g.2.1.isLt
  have u0:u.h=0:=h0
  have g0:g.grade=0:=by change g.2.1.val=0;omega
  rw [null_grade R B g.2.2 g0 n o U V]

/-- Centering a true probability law erases a separately projected constant in either slot. -/
theorem zero {Ω:Type*} [MeasurableSpace Ω] (ν:Measure Ω) [IsProbabilityMeasure ν]
    (F:Ω→ℂ) (all:∀u v,F u=F v) (a:Ω) (χ:ℂ→L[ℝ]ℝ) (Y:Ω→ℝ):
    (∫x,χ (F x)*Y x ∂ν)-(∫x,χ (F x) ∂ν)*(∫x,Y x ∂ν)=0 ∧
    (∫x,Y x*χ (F x) ∂ν)-(∫x,Y x ∂ν)*(∫x,χ (F x) ∂ν)=0:=by
  have eq:(fun x=>χ (F x))=fun _=>χ (F a):=funext (fun x=>congrArg χ (all x a))
  have l:(fun x=>χ (F x)*Y x)=(fun x=>χ (F a)*Y x):=funext (fun x=>by rw [all x a])
  have r:(fun x=>Y x*χ (F x))=(fun x=>Y x*χ (F a)):=funext (fun x=>by rw [all x a])
  rw [eq,l,r,integral_const_mul,integral_mul_const]
  simp

/-- Both centered responses see zero under any of the original held or cutoff probabilities. -/
theorem both (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4) (Q:Prescription B) (μ:ℝ)
    (k N p:ℕ) (live:R.family.ref 4≤N) (o:Site (R.family.side N p))
    (ν:Measure (Config G (R.family.side N p))) [IsProbabilityMeasure ν] (χ:ℂ→L[ℝ]ℝ)
    (Y:Config G (R.family.side N p)→ℝ):
    ∀f∈({R.family.O N p (source R B N p i) o,
      fun U=>ActualOriginalCalibratedColumns.weightedObservable R B Q (tag B i) μ _ o U k}:
        Finset (Config G (R.family.side N p)→ℂ)),
    (∫x,χ (f x)*Y x ∂ν)-(∫x,χ (f x) ∂ν)*(∫x,Y x ∂ν)=0 ∧
    (∫x,Y x*χ (f x) ∂ν)-(∫x,Y x ∂ν)*(∫x,χ (f x) ∂ν)=0:=by
  intro f mem
  apply zero ν f _ (1:Config G _) χ Y
  rcases Finset.mem_insert.mp mem with exact|last
  · subst f
    obtain ⟨c,hc⟩:=WilsonMatrixOriginalIndependentUnit.constant B R simple i low
    intro u v
    exact (hc N p live o u).trans (hc N p live o v).symm
  · rw [mem_singleton.mp last]
    exact nominal R B simple i low Q μ k _ o

end YM.Integration.WilsonMatrixOriginalIndependentCentering
