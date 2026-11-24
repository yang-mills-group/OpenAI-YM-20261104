import YM.Integration.WilsonMaxwellThermometerPublicUniform
import YM.Integration.WilsonMaxwellThermometerPositionCurrency

/-! The actual accepted extraction dates admit public compact prices before
every UV cutoff and every period, including the smallest period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicRoom
open Function Set Filter Finset Asymptotics Lattice Wilson RG Labels Source Extraction Table OPE OPE.Orbits Climb
open Trace.Pilot Next.UVStress Cells PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Atlas
open MergeProof.East XSpace XSpace.Cirrus XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicStation
open WilsonMaxwellThermometerPublicUniform
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "road"=>R.family.path.levels
local notation "Kβ"=>R.family.path.levels.clock.hatBeta

private theorem objective (X:ℝ):
    ∀ᶠ k:ℕ in atTop,X*(Kβ k)≤((R.family.S.denominator k).val:ℝ):=by
  let A:=R.family.path.levels
  have hv:(fun w:ℝ=>X*(A.clock.bar+G.slopeConstant*w))=o[atTop] Real.exp:=by
    have star (j:ℕ):(fun t:ℝ=>t^j)=o[atTop] Real.exp:=by
      simpa using isLittleO_pow_exp_pos_mul_atTop j (zero_lt_one' ℝ)
    simpa using! ((((star 0).const_mul_left A.clock.bar).add ((star 1).const_mul_left G.slopeConstant)).const_mul_left X)
  have due:=(hv.comp_tendsto A.S.divergent).def zero_lt_one
  filter_upwards [due] with k debt
  change X*A.clock.hatBeta k≤(A.S.denominator k).val
  calc _ ≤ |X*A.clock.hatBeta k|:=le_abs_self _
       _ ≤ Real.exp (A.S.scale k):=by
         simpa only [Calendar.hatBeta,Function.comp_def,one_mul,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le] using! debt
       _ = _:=by
         change Real.exp (Real.log (((A.S.denominator k).val:ℝ)⁻¹)⁻¹)=_
         rw [inv_inv,Real.exp_log (by exact_mod_cast (A.S.denominator k).pos)]

private theorem expense (simple:G.Simple)(d:ℕ):
    ∀ᶠ k:ℕ in atTop,∀b:ℝ,b≤Perch.y (Kβ k)→Station.mag road b k^d≤Kβ k:=by
  have h:(fun t:ℝ=>(d:ℝ)*t^3)=o[atTop] Real.exp:=by
    simpa using (isLittleO_pow_exp_pos_mul_atTop 3 (zero_lt_one' ℝ)).const_mul_left (d:ℝ)
  have K:=Station.hat_rate road simple
  have hi:∀ᶠ k:ℕ in atTop, _:=((h.comp_tendsto (Perch.y_rate.comp K)).def zero_lt_one)
  filter_upwards [hi,K.eventually (eventually_gt_atTop 1)] with k rent positive
  intro b hb
  have price:(d:ℝ)*(Perch.y (Kβ k))^3≤Real.exp (Perch.y (Kβ k)):=by
    apply (le_abs_self _).trans
    simpa only [Function.comp_def,one_mul,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le] using! rent
  rw [mag_bill,Perch.bill,←Real.exp_nat_mul]
  have e:Real.exp (Perch.y (Kβ k))=Real.log (Kβ k):=Real.exp_log (Real.log_pos positive)
  rw [← Real.exp_log (zero_lt_one.trans positive)]
  apply Real.exp_le_exp.mpr
  rw [mul_comm (d:ℝ)]
  calc _ ≤ Perch.boil (clim road k)*Perch.y (Kβ k)*d:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Perch.boil_pos _)) (Nat.cast_nonneg d)
       _ = (d:ℝ)*(Perch.y (Kβ k))^3:=by unfold Perch.boil;ring
       _ ≤ _ :=price.trans_eq e

theorem real (simple:G.Simple)(A:ℝ→Group R.family 6)
    (deep:Tendsto (fun r=>(A r).station.k) trail atTop)
    (live:∀ᶠ r in trail,(A r).station.wheel.r=r ∧
      5<(A r).station.b ∧ (A r).station.b≤Perch.y (Kβ (A r).station.k)):
    let k:=fun r=>(A r).station.k
    Tendsto (aperture R k) trail (𝓝 0) ∧ Spacious R k:=by
  let k:=fun r=>(A r).station.k
  have eqn:∀ᶠ r in trail,aperture R k r=(Station.mag road (A r).station.b (k r))⁻¹:=by
    filter_upwards [live,self_mem_nhdsWithin (s:=Set.Ioi 0)] with r hr pos
    rw [aperture,if_pos (show 0<r from pos)]
    exact WilsonMaxwellThermometerPositionCurrency.spacing R _ hr.1
  constructor
  · have run:=((Station.mag_rate road simple (by norm_num:0<(5:ℝ))).comp deep).inv_tendsto_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _:ℝ=>(0:ℝ)) (h:=fun r:ℝ=>(Station.mag road 5 (k r))⁻¹)
      tendsto_const_nhds run
    · exact Eventually.of_forall fun r=>(granted R k r).le
    filter_upwards [eqn,live] with r hr hb
    rw [hr]
    apply inv_anti₀ (Station.mag_pos ..)
    rw [mag_bill,mag_bill]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb.2.1.le (Perch.boil_pos _))
  intro d
  apply tendsto_atTop.mpr
  intro H
  have funded:=deep.eventually (objective R (max 1 H))
  have expensed:=deep.eventually (expense R simple d)
  filter_upwards [live,eqn,funded,expensed] with r hr due offset counted
  rw [due,inv_pow,le_inv_mul_iff₀ (pow_pos (Station.mag_pos ..) _)]
  apply le_trans _ offset
  calc _ ≤ Station.mag road (A r).station.b (k r)^d * max 1 H:=mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg (Station.mag_pos ..).le _)
       _ ≤ _ :=by rw [mul_comm];exact mul_le_mul_of_nonneg_left (counted _ hr.2.2) (zero_le_one.trans (le_max_left _ _))

end YM.Integration.WilsonMaxwellThermometerPublicRoom
end
