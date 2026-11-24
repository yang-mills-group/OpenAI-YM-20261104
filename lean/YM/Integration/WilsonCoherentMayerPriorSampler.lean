import YM.Integration.WilsonCoherentMayerPriorNumerical
import YM.Integration.WilsonCoherentMayerPriorFiling

/-! Positive-coupling value versus the independently prescribed, normalized finite Fk before any evaluation of the held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorSampler
open Filter Lattice Wilson RG Source Marker Precision Exterior
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction PhysicalWilsonActionConvention
open RG3.Script.Picnic MergeProof MergeProof.Accent WilsonMeasuredPathTaylor
open NativePaidPacketColors Comparison.Density.RenderM Next.SectorChange.Flat WilsonCoherentMayerPriorAtom
open scoped Classical ContDiff BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V] (R:Run G)
    {J:Request V}{A:NumericSchedule R.family J}{d:LocalFormal.Datum R.family (Stock.census V)}
    {F:AnalyticInput J A d}{K:NumericPrices A}{caps:Handoff.OutputCapacities}
local notation "YR" => RunFormalChain.fromRun R

theorem purchased (M:SignedAnalyticOutput caps (YR) K F)(c:V→ℂ)(nonzero:∀v,c v≠0)
    (s:(Stock.census V).Mode)(hs:s.val.Nonempty)(x:IndependentTests J.tests)
    (a:Directions G (R.family.side d.level d.period)){L:ℝ}(hL:0≤L)(legs:∀e,speed a e≤L)
    (q ord:ℕ)(enough:q+M.model.powerCap≤ord)(hord:ord≤J.order):
    let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let y:=VariableScaling.tests c (testInclusion J.tests x)
    2*L*|g|/A.outputWidth d.level≤1 →
    Poly.toll (fun v=>F.outputRadii v/F.kernelCosts v/‖c v‖) s*
      ‖(M.model.read y g (represent (g•labels a))).part s-
        ∑k∈Finset.range (ord+1),(g:ℂ)^k*
          (Order.observe (Stock.census V) J.order (Order.logMarked
            (Bulk.Fk (d.kernel (YR)) d.forest d.tag (F.colors y) (labels a) J.order)) k).part s‖≤
      ((powers M.model).card:ℝ)*(fee (A.outputWidth d.level) L q g*K.geometry d.level):=by
  intro g y small
  have positive:0<g:=Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt d.below)
  let E:=M.prescribed.extension y
  have amount:=WilsonCoherentMayerPriorNumerical.purchased (VariableScaling.paid c nonzero M.model M.paid)
    positive.ne' s hs x a hL legs q ord enough small E
    (fun u hu B=>by rw [VariableScaling.read];exact M.prescribed.value y u hu B)
    (fun B=>(M.prescribed.smooth y B).continuousAt)
    ((M.prescribed.smooth y (labels a)).of_le (by exact_mod_cast hord))
  rw [VariableScaling.read,←represent_field] at amount
  convert amount using 3
  unfold WilsonCoherentMayerPriorDiagonal.file
  apply congrArg (_-·)
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [E]
  rw [M.prescribed.coefficients y (labels a) k ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hord)]
  rfl
  rfl

end YM.Integration.WilsonCoherentMayerPriorSampler
