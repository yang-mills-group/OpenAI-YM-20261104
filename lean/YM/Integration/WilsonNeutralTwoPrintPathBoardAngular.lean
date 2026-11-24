import YM.Integration.WilsonNeutralTwoPrintPathBoardMean
import YM.Integration.WilsonNeutralTwoPrintPathJet

/-! Exact common-volume normalization of the independent fine-sheet sum at
every original tensor rank, using its own rooted fine-to-coarse selection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardAngular
open Function Finset Lattice RG Wilson
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider.Canvas
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalCensusDeckMean (mean)
open WilsonOriginalCensusOrbitCenters (layout escort shifted)
open WilsonNeutralTwoPrintPathFineFiber (seats)
open WilsonNeutralTwoPrintPathBoardSeats (homes copies)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonNeutralTwoPrintPathPageRead (lower)
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I]{n f X F:Side}
variable (P:Patch)(u:f.val=n.val*P.L.val)(v:F.val=X.val*P.L.val)(h:n.val∣X.val)(hf:f.val∣F.val)
  (S:Finset I)(o:S)(address:I→Site f)(root:Site X)(site:(S.erase o.val)→Site X)(base:Fin (Pages n X))
  (front:(page h (homes P u address o.val) base).val=root)
  (others:∀i:S.erase o.val,splitter h (site i)=homes P u address i.val)

open WilsonNeutralTwoPrintPathJet (diagonal)
variable {α V:Type}[Fintype α][NormedAddCommGroup V][NormedSpace ℝ V]
include front others in
theorem original (cap:ℕ)(Y:(I → Cover)→(r:ℕ)→Ten V (Site X × α) r)
    (test:V →L[ℝ] ℝ)(A:Site n × α→ℝ):
    (Pages n X:ℂ)⁻¹*∑p:S→Fin (Pages f F),
      ((diagonal cap (fun r z=>test (Y (seats P v h hf S address p o) r z)) (A ∘ lower h)):ℂ)=
    ∑r∈range (cap+1),mean h (plotted h S o.val root site (fun y=>Y y r) (Complex.ofRealCLM.comp test)
      (fun z=>∏i:Fin r,(A (z i):ℂ))):=by
  simp only [diagonal,Blue.toll,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro r _
  exact WilsonNeutralTwoPrintPathBoardMean.tensor P u v h hf S o address root site base front others r
    (fun y=>Y y r) (Complex.ofRealCLM.comp test) (fun z=>∏i:Fin r,(A (z i):ℂ))

end YM.Integration.WilsonNeutralTwoPrintPathBoardAngular
end
