import YM.Integration.WilsonCapturedPrimaryActiveArms
import YM.Integration.WilsonThermometerIntrinsicRoster

/-! The genuine separated incoming program on the already enrolled routes.
The costs are chosen before the routes, cuts, periods, and input amplitudes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
set_option quotPrecheck false
open WilsonThermometerIntrinsicRoster
variable {G : Gauge} (R : Run G)
local notation "A" => R.alloy.B.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ t ≥ D+3, ∀ᶠ k : ℕ in atTop, ∀ p N (hk:k≤N) (I : Type) [Fintype I] [DecidableEq I]
      (d : I→ℕ) (_:∀ i,d i≤D) (z:I→Site (R.family.side N p)),
      (∀ i j:I,i≠j → (R.family.path.levels.budget k).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R z k i)
          (WilsonThermometerOwnOffsetJoint.origins R z k j)) →
      ∀ (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i)),
        (∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) →
        ∀ (names:Census I) (y:(i:I)→Palette R.family (d i)), (∀i,size (y i) ≤ 1) →
          filed R d z y V r names hk t := by
  choose a pos caps using fun e : Fin (D+1)=>Cap.cost (line (primaryLetter e.val)) (e.val+2)
  let u : ℝ := 1+∑ e,a e
  have nonneg : 0≤∑ e,a e := Finset.sum_nonneg (fun e _=>(pos e).le)
  have up : 0<u := by dsimp [u];linarith
  have covered (e:ℕ) (he:e≤D) : Cap (e+2) (line (primaryLetter e)) u := by
    let l : Fin (D+1) := ⟨e,by omega⟩
    have c := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(pos j).le) (Finset.mem_univ l)
    exact (caps l).increase (by dsimp [u];linarith)
  obtain ⟨t,dt,starts⟩ := Many.startPay (C:=R.family) simple D u up
  obtain ⟨k₀,starts⟩ := eventually_atTop.mp starts
  have awake : ∀ᶠ k:ℕ in atTop,∀ e:Fin (D+1),Awake (C:=R.family) R.doors B k e.val :=
    Filter.eventually_all.mpr fun e=>(WilsonThermometerOffsetLedger.original R simple shop e.val).mono fun _ h=>h.1
  have grow := Many.beta_le' (C:=R.family) simple
  refine ⟨t,dt,?_⟩
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (D+3) t,
    awake,Many.theta_up (C:=R.family) (max 1 (2*u)) simple] with k late purse gates hot p N hk I _ _ d cap z room
  have gate (i:I) : Awake (C:=R.family) R.doors B k (d i) := gates ⟨d i,by have:=cap i;omega⟩
  intro V r H names y small
  have wallet (i:I) (j:ℕ) (hj:k≤j) :
      radius R t k j*(span R k j)^(d i+3)*β j^t ≤ 1 := by
    have lower := pow_le_pow_right₀ (span_one R hj) (show d i+3≤D+3 by have:=cap i;omega)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lower (radius_pos R t k j hj).le)
      (pow_nonneg (WardBin.hot _ _).le t)).trans (purse j hj)
  have last := starts N (late.trans hk)
  apply admitted R d z y V r simple hk names room H gate (fun i=>covered (d i) (cap i))
  · exact fun i=>top R (H i) (y i) (small i) up hk ⟨last.1,last.2 (d i) (cap i)⟩ (wallet i N hk)
  intro i j hj hn
  let X := span R k (j+1)
  let w := radius R t k (j+1)
  let b := β (j+1)
  have hkn := hj.trans j.le_succ
  have warm : max 1 (2*u) ≤ b := hot.trans (grow hkn)
  have fee : 2*u ≤ b^t := ((le_max_right 1 _).trans warm).trans
    (by simpa only [pow_one] using (pow_le_pow_right₀ ((le_max_left 1 _).trans warm) (show 1≤t by omega)))
  have smallcost := adjacent R (H i) (y i) (small i) up.le hj hn
  have wpos := (radius_pos R t k (j+1) hkn).le
  calc 2*w*charge R (r i) (y i) hj u ≤ 2*w*(X^(d i+3)*u) :=
          mul_le_mul_of_nonneg_left smallcost (by positivity : 0 ≤ 2*w)
       _ = w*X^(d i+3)*(2*u) := by ring
       _ ≤ w*X^(d i+3)*b^t := mul_le_mul_of_nonneg_left fee (mul_nonneg wpos (pow_nonneg (span_pos R k (j+1)).le _))
       _ ≤ 1 := wallet i (j+1) hkn

end YM.Integration.WilsonCapturedPrimaryWardRoster
