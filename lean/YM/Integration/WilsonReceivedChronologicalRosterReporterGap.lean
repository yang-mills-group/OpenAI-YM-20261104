import YM.Integration.WilsonAddressedPublicFirstRoseCaptureWidth
import YM.Integration.WilsonInvariantActionPosition

/-! Two actual fine reporting edges, measured from any fixed capture aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterReporterGap
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato Next.Rank.Station
open WilsonInvariantActionPosition (berth)
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "H" => R.family.path.levels.clock.hatBeta

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){M:ℝ}(mp:0<M):
    ∀ᶠ m:ℕ in atTop,∀{r:ℝ}{c:ℕ},a m ≤ r → M*r ≤ a c → c+2 ≤ berth R 5 m:=by
  let slope:=G.slopeConstant
  have sp:0 ≤ slope:=(Gauge.slopeConstant_pos simple).le
  filter_upwards [(hat_rate R.family.path.levels simple).eventually_ge_atTop
    (max (slope*Real.log M⁻¹) (7/M))] with m rich
  intro r c am cap
  let f:=berth R 5 m
  change c+2 ≤ f
  have hp:1 ≤ H m:=(R.family.path.levels.fits.delayed m).le
  have hp':0 < H m:=zero_lt_one.trans_le hp
  have ratio:a m/a c ≤ M⁻¹:=by
    rw [div_le_iff₀ (R.family.S.a_pos c)]
    apply (le_inv_mul_iff₀ mp).2
    exact (mul_le_mul_of_nonneg_left am mp.le).trans cap
  have log:=Real.log_le_log (div_pos (R.family.S.a_pos m) (R.family.S.a_pos c)) ratio
  rw [WilsonReflectedRelativeDate.ratio R] at log
  have cal:H c=H m+slope*(R.family.S.scale c-R.family.S.scale m):=by unfold Calendar.hatBeta;dsimp [slope];ring
  have pred:H c ≤ 2*H m:=by
    rw [cal]
    linarith only [mul_le_mul_of_nonneg_left log sp,(le_max_left _ _).trans rich]
  have price:6 < M*H m:=by
    have cash:7/M ≤ H m:=(le_max_right _ _).trans rich
    have funded:7 ≤ M*H m:=by simpa only [mul_comm] using (div_le_iff₀ mp).mp cash
    linarith only [funded]
  have reserve:6*H m<M*(H m)^5:=calc
    6*H m<(M*H m)*H m:=mul_lt_mul_of_pos_right price hp'
    _=M*(H m)^2:=by ring
    _≤M*(H m)^5:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by decide:2≤5)) mp.le
  have upper:(H m)^5*a f ≤ r:=by
    calc
      _=a f*(H m)^5:=mul_comm _ _
      _≤a m:=(WilsonInvariantActionPosition.arrival R 5 m).2
      _≤r:=am
  by_contra! missing
  have hf:f ≤ c+1:=by omega
  have paid:=WilsonAddressedPublicFirstRoseCaptureWidth.block R simple slow (c:=c) (j:=c) le_rfl
  have cost:((R.family.S.block c).val:ℝ)≤6*H m:=by linarith only [paid,pred]
  have neighbour:a c=((R.family.S.block c).val:ℝ)*a (c+1):=by
    rw [R.family.S.a_step,mul_div_cancel₀ _ (by exact_mod_cast (R.family.S.block c).property.ne')]
  exact (not_lt_of_ge cap) (calc
    a c=_:=neighbour
    _≤(6*H m)*a f:=mul_le_mul cost (R.family.S.strictAnti.antitone hf) (R.family.S.a_pos _).le (by positivity)
    _<(M*(H m)^5)*a f:=mul_lt_mul_of_pos_right reserve (R.family.S.a_pos _)
    _≤M*r:=by rw [mul_assoc];exact mul_le_mul_of_nonneg_left upper mp.le)

end YM.Integration.WilsonReceivedChronologicalRosterReporterGap
