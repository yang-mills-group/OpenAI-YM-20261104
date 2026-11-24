import YM.Integration.WilsonNeutralTwoPrintPathBoardSeats

/-! Exact common-volume normalization of the independent fine-sheet sum at
every original tensor rank, using its own rooted fine-to-coarse selection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardMean
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
include front others in
theorem original (T:(I → Cover)→ℂ):
    (Pages n X:ℂ)⁻¹*∑p:S→Fin (Pages f F),T (seats P v h hf S address p o)=
      mean h (fun d=>∑p:(S.erase o.val)→Fin (Pages n X),T (layout h S o.val (d.val+root) (shifted h site d) p)):=by
  let read (s:S→Fin (Pages f F)):=T (seats P v h hf S address s o)
  change (Pages n X:ℂ)⁻¹*∑p,read p=_
  rw [←(copies P u v h hf S address).sum_comp read,
    WilsonOriginalCensusPageOrbits.average h S o.val o.prop (homes P u address) base]
  unfold mean
  congr 1
  apply sum_congr rfl
  intro d _
  dsimp only
  rw [←(escort h site d).sum_comp (fun p=>T (layout h S o.val (d.val+root) (shifted h site d) p))]
  apply sum_congr rfl
  intro p _
  exact congrArg T (WilsonNeutralTwoPrintPathBoardSeats.original P u v h hf S o address root site base front others d p)

variable {α V:Type}[Fintype α][NormedAddCommGroup V][NormedSpace ℝ V]
include front others in
theorem tensor (r:ℕ)(Y:(I → Cover)→Ten V (Site X × α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):
    (Pages n X:ℂ)⁻¹*∑p:S→Fin (Pages f F),∑x:Fin r→Site X × α,
      test (Y (seats P v h hf S address p o) x)*weights (lower h ∘ x)=
        mean h (plotted h S o.val root site Y test weights):=by
  rw [original P u v h hf S o address root site base front others
    (fun y=>∑x:Fin r→Site X × α,test (Y y x)*weights (lower h ∘ x))]
  unfold mean
  congr 1
  apply sum_congr rfl
  intro d _
  dsimp only [plotted]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  rw [Finset.sum_mul]

end YM.Integration.WilsonNeutralTwoPrintPathBoardMean
end
