import YM.Integration.WilsonPositionProgramTrialCollarKinetic

/-! Chronological dates for the actual finite planting mesh. The planting
date is given in advance, and the earlier blocks supply the quadratic reserve. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialOpticalBand
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
open WilsonPositionProgramTrialCollarMesh (index Corridor)
open WilsonInvariantActionPosition (berth)
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) (D : XSpace.Run)
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "hat" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

structure Band (K : ℕ→ℕ) (stage : ℕ) where
  reporter : ℕ
  lower : ℕ→ℕ
  span : ℕ→ℕ
  mesh : ℕ→ℕ
  powers : ℕ→ℕ→ℕ
  blocks : ∀ t k, (R.family.S.block (lower t+k)).val=D.ratio^(powers t k)
  extent : ∀ t, elapsed (powers t) (span t)=D.reserve*(mesh t)*(mesh t)+mesh t
  ready : ∀ t, stage ≤ lower t
  top : ∀ t, lower t+span t=K (reporter+t)
  spacing : ∀ t, a (K (reporter+t)) / a (reporter+t)=(D.step (mesh t)).spacing
  room : ∀ t, Λ (lower t) ≤ (mesh t:ℝ)*Real.log D.ratio
  cofinal : Tendsto mesh atTop atTop

def Bracket (K : ℕ→ℕ) (A : ℝ) : Prop := ∀ᶠ m in atTop,
  m<K m ∧ Λ m ≤ Real.log (a m/a (K m)) ∧ Real.log (a m/a (K m)) ≤ A*Λ m

theorem elected {axis : Axis} {ε : ℝ} (purchase : WilsonPositionProgramArithmetic.course simple axis ε R.kit)
    {d : ℕ} (hd : 0<d) (ratio : D.ratio=(3:ℕ)^d) (stage : ℕ)
    (K : ℕ→ℕ) {A : ℝ} (nonneg : 0≤A) (charged : Bracket R K A) : Nonempty (Band R D K stage) := by
  obtain ⟨start,w,_,dates⟩ := WilsonPositionProgramTrialCollarMesh.original R simple D purchase hd ratio
  have shift : Tendsto (fun n:ℕ=>start+n) atTop atTop :=
    tendsto_atTop_mono (fun n=>Nat.le_add_left n start) tendsto_id
  let j (n:ℕ):=K (start+n)-(start+n)
  have issued : ∀ᶠ n in atTop, start+n+j n=K (start+n) ∧
      Λ (start+n) ≤ (index w n (j n):ℝ)*Real.log D.ratio ∧
      ∃ b, Corridor R D start w stage n (j n) b := by
    filter_upwards [dates stage A nonneg,shift.eventually charged] with n buy yes
    have atDate : start+n+j n=K (start+n) := Nat.add_sub_of_le yes.1.le
    obtain ⟨b,held⟩:=buy (j n) (atDate ▸ yes.2.2)
    have length := held.spacing
    rw [atDate] at length
    refine ⟨atDate,?_,b,held⟩
    have exactLog : Real.log (a (start+n)/a (K (start+n))) =
        (index w n (j n):ℝ)*Real.log D.ratio := by
      rw [←inv_div,length,Real.log_inv]
      change -Real.log ((D.den _:ℝ)⁻¹)=_
      simp [XSpace.Run.den,Real.log_pow]
    exact yes.2.1.trans_eq exactLog
  obtain ⟨n₀,ready⟩ := eventually_atTop.mp issued
  let n (t:ℕ):=n₀+t
  let reporter:=start+n₀
  have clock (t:ℕ) : start+n t=reporter+t := (Nat.add_assoc ..).symm
  have pay (t:ℕ) := ready (n t) (Nat.le_add_right n₀ t)
  choose b invoice using (fun t=> (pay t).2.2)
  let I (t:ℕ) := index w (n t) (j (n t))
  refine ⟨⟨reporter,(fun t=>start+b t),(fun t=>n t+j (n t)-b t),I,(fun t=>next w (b t)),
    (fun t=>(invoice t).blocks),(fun t=>(invoice t).total),(fun t=>(invoice t).eligible),?_,?_,?_,?_⟩⟩
  · intro t
    rw [←clock,←(pay t).1]
    have hb := (invoice t).below
    omega
  · intro t
    rw [←clock,←(pay t).1]
    exact (invoice t).spacing
  · intro t
    exact ((RG16.Literal.lambda_mono R.family simple).monotone (Nat.add_le_add_left (invoice t).below start)).trans (pay t).2.1
  · apply tendsto_atTop.mpr
    intro k
    have grow : Tendsto n atTop atTop := tendsto_atTop_mono (fun t=>Nat.le_add_left t n₀) tendsto_id
    have high := (RG16.Literal.lambda_leads R.family simple).comp (shift.comp grow)
    have positive := Real.log_pos (show 1<(D.ratio:ℝ) by exact_mod_cast (show 1<D.ratio from (by decide : 1<3).trans_le D.large))
    filter_upwards [high.eventually_ge_atTop ((k:ℝ)*Real.log D.ratio)] with t enough
    exact_mod_cast (mul_le_mul_iff_of_pos_right positive).mp (enough.trans (pay t).2.1)

include simple in
theorem bracket (slow:WilsonWindowReportingPace.Slow R.kit) {t:ℕ} (long:2≤t) :
    Bracket R (berth R t) (t+1) := by
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t zero_lt_one,
    (WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).eventually_ge_atTop 2] with m sale late
  have hp := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have low := Real.log_le_log (pow_pos hp t) sale.2.1
  have high := Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) sale.2.2
  rw [Real.log_pow] at low
  rw [Real.rpow_one,←pow_succ,Real.log_pow] at high
  change 2≤Real.log (hat m) at late
  change _ ∧ 2+Real.log (hat m)≤_ ∧ _≤((t:ℝ)+1)*(2+Real.log (hat m))
  have double := mul_le_mul_of_nonneg_right (show (2:ℝ)≤(t:ℝ) by exact_mod_cast long)
    (Real.log_nonneg (R.family.path.levels.fits.delayed m).le)
  push_cast at high
  exact ⟨sale.1,by linarith only [low,double,late],by linarith only [high,(Nat.cast_nonneg t:0≤(t:ℝ))]⟩

end YM.Integration.WilsonPositionProgramTrialOpticalBand
end
