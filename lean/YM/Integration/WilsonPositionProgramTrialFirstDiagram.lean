import YM.Integration.WilsonPositionProgramTrialFeynmanFigure
import YM.Pert.First.OneArray

/-! The ground and the first Wilson interaction of the actual planted
position figure after its own total field-order shift. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
namespace YM.Integration.WilsonPositionProgramTrialFirstDiagram
open Function Finset Lattice Gauge Wilson PhysicalNext.Repeat.Legato
open Precision FVA2 FVA2.Trans SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open FormalOPE.RG10 RG Exterior Comparison.RG02 PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart PertExtension.GaussianScore
open MeasureTheory PowerSeries WilsonPositionProgramCopyTop
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I→ℕ) (o : I → Cover)
    (b : ∀i,(R.family.labels.level (d i)).Index)
local notation "O" => planted R p d o b
local notation "dep" => YM.RegulatorIR.FVAAlt2.Kick.depthF univ d b
local notation "raw" => ChartC (fun A : Potential G p.side => (O (positiveLinks A):ℂ))

def term (q : ℕ) (A : Potential G p.side) : ℂ := coeff (dep+q) (raw A)
def quotient (A : Potential G p.side) : ℂ⟦X⟧ := PowerSeries.mk (fun q=>term R p d o b q A)

theorem entries : Fentry raw = X^dep*Fentry (quotient R p d o b) := by
  let f:=fun A : Potential G p.side => (O (positiveLinks A):ℂ)
  let low:=WilsonPositionProgramTrialFeynmanFigure.prepared R p d o b
  have ready:Ready (quotient R p d o b):=by
    intro k
    simpa only [quotient,coeff_mk,term] using chart_ready f (dep+k)
  rw [←entry_scale ready]
  apply congrArg Fentry
  funext A
  change ChartC f A=X^dep*quotient R p d o b A
  ext j
  rw [coeff_X_pow_mul']
  by_cases h:dep≤j
  · rw [if_pos h,quotient,coeff_mk,term,Nat.add_sub_of_le h]
  · rw [if_neg h,ChartC,coeff_mk]
    change (j.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ j f 0 (fun _=>A)=0
    rw [show iteratedFDeriv ℝ j f 0=0 from low.vanish j (Nat.lt_of_not_ge h)]
    simp

theorem finite (D : ChartRatio G) (law : LocalRatio D) (T : p.Tree) (q : ℕ) :
    coeff (q+dep) (normalized R p d o b T)=coeff q (Fentry (quotient R p d o b)) := by
  rw [WilsonPositionProgramCopyTop.original R p d o b D law T q,
    ←coeff_X_pow_mul _ dep q,←entries]
  rw [WilsonPositionProgramTrialFeynmanFigure.original R p d o b D law,cscale,coeff_mk]
  rfl

theorem ground (D : ChartRatio G) (law : LocalRatio D) (T : p.Tree) :
    coeff dep (normalized R p d o b T)=
      ∫ y,term R p d o b 0 (expand G p.side y) ∂data G p.side := by
  have h:=finite R p d o b D law T 0
  rw [Nat.zero_add] at h
  rw [h,coeff_zero_eq_constantCoeff]
  change constantCoeff (Pert.Orb.normalize ((quotient R p d o b) ∘ blue G p.side))=_
  rw [Pert.Warp.normalize_zero]
  apply integral_congr_ae
  filter_upwards with y
  change constantCoeff (quotient R p d o b (expand G p.side y))=_
  rw [←coeff_zero_eq_constantCoeff_apply,quotient,coeff_mk]

theorem original (simple : G.Simple) (D : ChartRatio G) (law : LocalRatio D) (T : p.Tree) :
    coeff (1+dep) (normalized R p d o b T)=
      ∫ y,(Pert.First.vertexW y:ℂ)*term R p d o b 0 (expand G p.side y)+
        term R p d o b 1 (expand G p.side y) ∂data G p.side := by
  rw [finite R p d o b D law T 1]
  change coeff 1 (Pert.Orb.normalize ((quotient R p d o b) ∘ blue G p.side))=_
  rw [Pert.First.normalize_one]
  apply integral_congr_ae
  filter_upwards with y
  change coeff 1 (weight G p.side y)*constantCoeff (quotient R p d o b (expand G p.side y))+
    coeff 1 (quotient R p d o b (expand G p.side y))=_
  rw [Pert.First.has_first simple,Pert.First.total_vertex,←coeff_zero_eq_constantCoeff_apply,
    quotient,coeff_mk,coeff_mk]

end YM.Integration.WilsonPositionProgramTrialFirstDiagram
