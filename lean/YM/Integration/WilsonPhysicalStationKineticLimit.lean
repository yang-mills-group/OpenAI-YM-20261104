import YM.Integration.WilsonPhysicalStationCofinalLower
import YM.Integration.WilsonIndependentRegisteredActuators

/-! The actual positive adjacent thermal ratio has a positive subsequential
limit on the same original cofinal filter as the appointed physical sources. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationKineticLimit
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato Next.Rank.Price
open Push.RelayDifference Next.UVStress
open scoped Topology

variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "θ" => (A).clock.threshold

def coupling (N p m:ℕ):ℝ:=(Real.sqrt (R.family.path.β N p m))⁻¹
def transit (m k:ℕ)(i:Cutoffs):ℝ:=coupling R i.1 i.2 m / coupling R i.1 i.2 k

theorem bracket (hg:G.Simple):
   ∀ᶠ m:ℕ in atTop,∀ N p:ℕ,m < N→1/8 ≤ transit R m (m+1) (N,p)∧transit R m (m+1) (N,p) ≤ 12:=by
  filter_upwards [WilsonIndependentRegisteredActuators.original R hg] with m issued
  intro N p live
  obtain ⟨s0,s1,ledger⟩:=issued
  obtain ⟨low,high⟩:=ledger N p live
  have t0:0 < θ m:=((A).budget m).threshold_pos
  have t1:0 < θ (m+1):=((A).budget (m+1)).threshold_pos
  have p0:=shrink_pos R.family R.makes live.le p
  have p1:=shrink_pos R.family R.makes live p
  let P:=fun j=>shrink R.family j N p
  have budget (j:ℕ)(warm:0 < θ j):P j*θ j=coupling R N p j:=
    div_mul_cancel₀ _ warm.ne'
  have g1:0 < coupling R N p (m+1):=(budget (m+1) t1).symm.trans_gt (mul_pos p1 t1)
  have down:=mul_le_mul high ((div_le_iff₀ t0).mp s1) t1.le (show 0 ≤ 4*P m by positivity)
  have up:=mul_le_mul low ((div_le_iff₀ t1).mp s0) t0.le (show 0 ≤ 6*P (m+1) by positivity)
  change P (m+1)*θ (m+1)  ≤  (4*P m)*(2*θ m) at down
  change P m*θ m  ≤  (6*P (m+1))*(2*θ (m+1)) at up
  change 1/8 ≤ coupling R N p m/coupling R N p (m+1) ∧ coupling R N p m/coupling R N p (m+1) ≤ 12
  constructor
  · apply (le_div_iff₀ g1).2
    rw [←budget _ t1,←budget _ t0]
    nlinarith only [down]
  · apply (div_le_iff₀ g1).2
    rw [←budget _ t1,←budget _ t0]
    nlinarith only [up]

theorem original (m k:ℕ) {b:Filter Cutoffs}[b.NeBot]
    (paid:∀ᶠ c in b,1/8 ≤ transit R m k c ∧ transit R m k c ≤ 12):
    ∃ l:Filter Cutoffs,l ≤ b∧l.NeBot∧∃ slope:ℝ, 1/8 ≤ slope∧slope ≤ 12∧
      Tendsto (transit R m k) l (𝓝 slope):=by
  have coat:∀ᶠ c in b,‖transit R m k c‖ ≤ 12:=by
    filter_upwards [paid] with c h
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith only [h.1])]
    exact h.2
  obtain ⟨l,le,good,x,hx⟩:=finite_extract (𝓛:=b) (transit R m k) 12 coat
  letI:=good
  have bounds:=paid.filter_mono le
  exact ⟨l,le,good,x,ge_of_tendsto hx (bounds.mono (fun _ e=>e.1)),
     le_of_tendsto hx (bounds.mono (fun _ e=>e.2)),hx⟩

end YM.Integration.WilsonPhysicalStationKineticLimit
end
