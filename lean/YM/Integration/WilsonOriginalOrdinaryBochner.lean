import YM.Integration.WilsonOriginalSeparatedDatedHearing

/-! Bochner integrability of the two ordinary fields submitted to the same original
Haar integral. Each marked component is charged at its own rooted radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOrdinaryBochner
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open Push Push.Local Push.AbsoluteSums Multi Push.AbsoluteSums.Animals
open Comparison.RG02.Cumulants WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]{J:Census V}

omit [Fintype V] in
private theorem integral {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsFiniteMeasure μ]
    {d:Ω→ℝ}(quiet:Envelope d)(F:Ω→Poly J)(entries:∀s:J.Mode,Envelope (fun U=>(F U).part s)):
    Integrable (fun U=>(d U:ℂ) • F U) μ:=by
  have eqn:F=fun U=>∑s:J.Mode,Poly.send s ((F U).part s):=funext fun U=>(Poly.studs _).symm
  have mf:Measurable F:=by
    rw [eqn]
    exact Finset.measurable_sum _ fun s _=>(Overlay.Bands.sends s).measurable.comp (entries s).meas
  choose pay bound using fun s=>(entries s).cost
  have positive (v:V):0<(1:ℝ):=zero_lt_one
  obtain ⟨c,hc,priced⟩:=Poly.equivalent_norm (R:=J) positive
  let cap:=∑s:J.Mode,Poly.toll (fun _:V=>(1:ℝ)) s*pay s
  have cost (U:Ω):‖F U‖ ≤ cap*c:=by
    apply (priced _).trans
    apply mul_le_mul_of_nonneg_right _ hc
    exact Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_left (bound s U) (Poly.worth positive s).le
  obtain ⟨C,paid⟩:=quiet.cost
  apply Integrable.of_bound ((Complex.continuous_ofReal.measurable.comp quiet.meas).smul mf).aestronglyMeasurable (C*(cap*c))
  exact ae_of_all _ fun U=>by
    change ‖(d U:ℂ) • F U‖ ≤ C*(cap*c)
    rw [norm_smul,Complex.norm_real]
    exact mul_le_mul (paid U) (cost U) (norm_nonneg _) ((norm_nonneg _).trans (paid U))

variable {p:BudgetPoint}{X ι:Type}{o:V→Site n}

theorem regular [Countable ι](ρ:Rep G n)(quiet:Envelope ρ.eval)(L:Lamps X ι G p o J)
    {w:V→ℝ}(hw:∀v,0<w v){a E:ℝ}(width:0 ≤ a)(paid:L.Paid w p.B a E)(x:X):
    Integrable (fun U=>(ρ.eval U:ℂ) • Poly.pass (L.log x U)) (prior G n):=by
  apply integral (prior G n) quiet
  intro s
  refine ⟨WilsonOriginalBetweenFiledPrints.ordinary L w hw width paid x s,
    ∑q∈shards J s,∏t∈q.val,(Poly.toll w t.val)⁻¹*E,?_⟩
  intro U
  rw [YM.RG02.Marks.pass_partition (L.quiet_of_hasSum x U (paid.sums width hw x U)) s]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro q _
  rw [norm_prod]
  apply prod_le_prod (fun t _=>norm_nonneg _)
  intro t _
  obtain ⟨v,hv⟩:=t.property
  exact WilsonCenteredRegularHit.component L w hw width paid x U t.val v hv

theorem unmasked [Countable ι](ρ:Rep G n)(quiet:Envelope ρ.eval)(L:Lamps X ι G p o J)
    {w:V→ℝ}(hw:∀v,0<w v){a C:ℝ}(width:0 ≤ a)(sold:Gross L w p.B a C)(x:X):
    Integrable (fun U=>(ρ.eval U:ℂ) • Poly.pass (bare L x U)) (prior G n):=by
  apply integral (prior G n) quiet
  intro s
  refine ⟨WilsonReceivedWholeFieldHot.borel L hw width sold x s,
    (Poly.toll w s)⁻¹*WilsonReceivedWholeFieldHot.charge s C,?_⟩
  intro U
  exact (le_inv_mul_iff₀ (Poly.worth hw s)).mpr (WilsonReceivedWholeFieldHot.ordinary L hw width sold x U s)

end YM.Integration.WilsonOriginalOrdinaryBochner
end
