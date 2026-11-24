import YM.Integration.WilsonOlderFreshPointChart

/-! If the two grid paths have common fine digits, the full nonlinear
normalized upper programme, including all its held-link charts, agrees
before taking either regulator limit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 130000
noncomputable section
namespace YM.Integration.WilsonNeutralReportCommonTail
open FormalBulk08 Lattice Wilson City Pose RG Roof Stationary Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free
open Lotus Shore Mesa Gorge Cork Rift Lava Kemp Glide Bank Dawn Wine Rial Dove
open WilsonNeutralPointCourse PhysicalNext.Repeat.Legato
open scoped Classical
variable {G:Gauge}{d D:ℕ}(R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
local notation "axes" => Letter (R.family.labels.level d)
variable {δ γ:∀i,Site (R.family.S.block i)}
private theorem at_edge (digit:∀i,Site (R.family.S.block i)){N i:ℕ}(hi:i<N):
    WilsonNeutralPointCourse.filed R wood a depth digit N i=reset R wood a digit N i (WilsonNeutralPointCourse.filed R wood a depth digit N (i+1)):=by
  unfold WilsonNeutralPointCourse.filed
  conv_lhs=>rw [show N-i=(N-(i+1))+1 by omega]
  rfl

theorem filed {N i:ℕ}(hi:i ≤ N)(same:∀j,i ≤ j → j<N → δ j=γ j):
    WilsonNeutralPointCourse.filed R wood a depth δ N i=WilsonNeutralPointCourse.filed R wood a depth γ N i:=by
  induction hi using Nat.decreasingInduction with
  | self=>rw [top,top]
  | of_succ j live ih=>
    rw [at_edge R wood a depth δ live,at_edge R wood a depth γ live,
      ih (fun k lo up=>same k (by omega) up)]
    unfold reset forward
    rw [same j le_rfl live]

theorem transfer {N i:ℕ}(hi:i<N)(same:∀j,i ≤ j → j<N → δ j=γ j):
    WilsonNeutralPointCourse.transfer R wood a depth δ N i=WilsonNeutralPointCourse.transfer R wood a depth γ N i:=by
  unfold WilsonNeutralPointCourse.transfer
  rw [filed R wood a depth (by omega: i+1 ≤ N) (fun j lo up=>same j (by omega) up)]
  unfold forward
  rw [same i le_rfl hi]

theorem field {N i:ℕ}(hi:i ≤ N)(same:∀j,i ≤ j → j<N → δ j=γ j)(b:axes)(f:Studio D):
    WilsonOlderFreshPointGauge.field R wood a depth i b (⟨N,hi,δ⟩,f)=
      WilsonOlderFreshPointGauge.field R wood a depth i b (⟨N,hi,γ⟩,f):=by
  unfold WilsonOlderFreshPointGauge.field
  change WilsonNeutralPointCourse.filed R wood a depth δ N i b f=WilsonNeutralPointCourse.filed R wood a depth γ N i b f
  rw [filed R wood a depth hi same]

theorem chart {N i:ℕ}(hi:i ≤ N)(same:∀j,i ≤ j → j<N → δ j=γ j)(b:axes)(f:Studio D):
    WilsonOlderFreshPointChart.chart R wood a depth i b (⟨N,hi,δ⟩,f)=
      WilsonOlderFreshPointChart.chart R wood a depth i b (⟨N,hi,γ⟩,f):=by
  funext n x
  unfold WilsonOlderFreshPointChart.chart
  rw [field R wood a depth hi same]

end YM.Integration.WilsonNeutralReportCommonTail
