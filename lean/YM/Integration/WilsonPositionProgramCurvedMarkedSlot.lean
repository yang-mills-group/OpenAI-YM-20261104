import YM.Integration.WilsonPositionProgramCurvedOccupiedPrice
import YM.Integration.WilsonOriginalCoverJetColors

/-! Re-enter a marked deposit through the true fine-link chart, using its own Laurent grade and all angular coefficients. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramCurvedMarkedSlot
open Function Filter Finset Lattice RG Exterior Tree Precision Marker Multi
open Comparison.RG02 Assembly Valence Adjacent
open YM.Wilson FVA1Physical.Wilson QuadraticLocal.Earn QuadraticLocal.Sunrise
open WilsonPositionProgramAngularChart
open scoped Topology Classical ContDiff BigOperators

variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)
  {V:Type}[DecidableEq V]{R:Census V}

theorem deposited (W Y:Bulk.Colors R G f)(s:Hot R)
    (hW:GradeAt (W.power s) (Bulk.projected (W.mark s)))(hY:GradeAt (Y.power s) (Bulk.projected (Y.mark s)))
    (k:ℕ)(b:Bulk.SliceDir S F G):
    jet (Bulk.markFn S F W s) k (1,b)-jet (Bulk.markFn S F Y s) k (1,b) =
    jet ((Bulk.projected (W.mark s)-Bulk.projected (Y.mark s)) ∘ chart (Work.F03.axisLog F)) k (1,b) := by
  have equal: (Bulk.markFn S F W s-Bulk.markFn S F Y s)=ᶠ[𝓝 0]
      ((Bulk.projected (W.mark s)-Bulk.projected (Y.mark s)) ∘ chart (Work.F03.axisLog F)) := by
    have prior:=continuous_snd.tendsto (0:Bulk.Joint S F (G:=G))
    filter_upwards [prior.eventually (Work.F03.inclusion_works F)] with x hx
    change W.mark s x.1 (Work.F03.live F x.2)-Y.mark s x.1 (Work.F03.live F x.2)=
      W.mark s x.1 (represent (Work.F03.axisLog F x.2))-Y.mark s x.1 (represent (Work.F03.axisLog F x.2))
    rw [hx]
  have readyW:ContDiffAt ℝ ω (Bulk.markFn S F W s) 0 := (Bulk.joint_receipt S F hW).smooth
  have readyY:ContDiffAt ℝ ω (Bulk.markFn S F Y s) 0 := (Bulk.joint_receipt S F hY).smooth
  unfold Assembly.jet
  rw [← (equal.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_sub_apply (readyW.of_le le_top) (readyY.of_le le_top)]
  exact (smul_sub _ _ _).symm

theorem original (W Y:Bulk.Colors R G f)(s:Hot R)(same:W.power s=Y.power s)
    (hW:GradeAt (W.power s) (Bulk.projected (W.mark s)))(hY:GradeAt (Y.power s) (Bulk.projected (Y.mark s)))
    (p v:ℕ)(ε:ℝ)(he:0≤ε)
    (bound:∀t≤p,∀x:fieldDir G f 1,‖(Air.discharge W t x).part s.val-(Air.discharge Y t x).part s.val‖ ≤ ε*(1+‖x‖)^v)
    (b:Bulk.SliceDir S F G):
    ‖jet (Bulk.markFn S F W s) (W.power s+p) (1,b)-jet (Bulk.markFn S F Y s) (Y.power s+p) (1,b)‖ ≤
      2*(2*WilsonPositionProgramCurvedAngularPrice.price G (W.power s+p) v+1)*
        (ε*(1+‖b‖)^((W.power s+p)*v)) := by
  rw [← same,deposited F W Y s hW hY]
  apply WilsonPositionProgramCurvedOccupiedPrice.original F _ (hW.smooth.sub hY.smooth) _ v ε he _ b
  intro d hd x
  have diff:jet (Bulk.projected (W.mark s)-Bulk.projected (Y.mark s)) d (1,x) =
      jet (Bulk.projected (W.mark s)) d (1,x)-jet (Bulk.projected (Y.mark s)) d (1,x) := by
    unfold Assembly.jet
    rw [iteratedFDeriv_sub_apply (hW.smooth.of_le le_top) (hY.smooth.of_le le_top)]
    exact smul_sub _ _ _
  change ‖Assembly.jet (Bulk.projected (W.mark s)-Bulk.projected (Y.mark s)) d (1,x)‖ ≤ _
  rw [diff]
  by_cases below:d<W.power s
  · rw [hW.jet_z _ below,hY.jet_z _ (same ▸ below),sub_self,norm_zero]
    positivity
  have pay:=bound (d-W.power s) (by omega) x
  rw [Air.discharge,Multi.part_lit _ s,Air.discharge,Multi.part_lit _ s] at pay
  have w:W.power s+(d-W.power s)=d:=by omega
  have y:Y.power s+(d-W.power s)=d:=by omega
  simpa only [w,y] using pay

end YM.Integration.WilsonPositionProgramCurvedMarkedSlot
end
