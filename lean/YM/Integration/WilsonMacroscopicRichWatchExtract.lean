import YM.Integration.WilsonMacroscopicRichSingleWatch
import YM.Next.UV_STRESS.Vary

/-! One subfilter for the actual raw counterterm, fixed before all exterior watches. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchExtract
open Function Filter Spec OPE OPE.Orbits Lattice Cells Wilson Next.UVStress
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

theorem original (F:Final C f S)(h:ℕ){l:Filter (ℕ×ℕ)}[l.NeBot](order:l≤f.fuse)
    (z:ℕ×ℕ→C.label h)(x:C.label h)(price:ℝ)
    (bill:∀ᶠ i in l,‖z i-x‖≤price):
    ∃l':Filter (ℕ×ℕ),l'≤l ∧ l'.NeBot ∧ ∃raw:C.label h,
      Tendsto z l' (𝓝 raw) ∧ ‖raw-x‖≤price ∧ ∀W:Watch C,
        Tendsto (fun i:ℕ×ℕ=>moment (C.beta i.1 i.2) (fun U=>C.O i.1 i.2 (z i) 0 U*W.plot i.1 i.2 U))
          l' (𝓝 (W.tester S h (S.project h raw))):=by
  have bound:∀ᶠ i in l,‖z i‖≤price+‖x‖:=by
    filter_upwards [bill] with i fit
    exact (norm_le_norm_sub_add (z i) x).trans (add_le_add fit le_rfl)
  obtain ⟨l',narrow,proper,raw,coherent⟩:=finite_extract z (price+‖x‖) bound
  letI:l'.NeBot:=proper
  have projected:=((S.project h).toContinuousLinearMap.continuous.tendsto raw).comp coherent
  have close:‖raw-x‖≤price:=le_of_tendsto (coherent.sub_const x).norm (bill.filter_mono narrow)
  refine ⟨l',narrow,proper,raw,coherent,close,?_⟩
  intro W
  exact WilsonMacroscopicRichSingleWatch.moving F W h (narrow.trans order) z (price+‖x‖)
    (bound.filter_mono narrow) (S.project h raw) projected

end YM.Integration.WilsonMacroscopicRichWatchExtract
