import YM.Integration.WilsonPositionScaleLawHome

/-! The original one-home position purse on any predeclared closed positive ratio window, with lower endpoint chosen independently of the physical data. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawWindow
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionScaleLawHome (bank smeared)
open scoped Topology Classical BigOperators

class RangeSpec where
  left : ℝ
  positive : 0 < left

abbrev Ratio [Win:RangeSpec]:={t:ℝ // t∈Icc Win.left 1}
abbrev sweep [RangeSpec]:Filter (ℝ×Ratio):=trail ×ˢ ⊤

variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)

theorem original (lead:Leading F J)(d:ℕ):
    (V.survey d).Via (fun z:ℝ×Ratio=>bank F J V d z.1 z.2.val) (u:=sweep):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let W:=(V.survey d).scope i
  let v(k:Fin W.n):=Module.finBasis ℝ (Sec G d) (j k)
  have p:=smeared F J V lead v W.t (b:=1) (c:=Win.left) Win.positive he
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually p] with z hz
  rw [dist_eq_norm]
  exact hz z.2.val z.2.property

end YM.Integration.WilsonPositionScaleLawWindow
end
