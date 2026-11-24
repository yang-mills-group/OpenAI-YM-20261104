import YM.Integration.WilsonThermometerReflectedRoster

/-! The original reflected joint is funded at its fully restored source amplitudes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFundedRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerReflectedTrajectory
open scoped Classical Topology
open WilsonThermometerReflectedRoster
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {N p k:ℕ} {I:Type}
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "β" => R.alloy.B.a.clock.hatBeta

theorem radius_succ (t:ℕ) {k j:ℕ} (h:k≤j) :
    radius R (t+1) k j = (β k)⁻¹ * radius R t k j:=by
  induction j,h using Nat.le_induction with
  | base=>rw [radius_start,radius_start,pow_succ,mul_inv_rev]
  | succ j hj ih=>rw [radius_next R _ _ _ hj,radius_next R _ _ _ hj,ih];ring

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
    ∃ t ≥ D+3,∀ᶠ k:ℕ in atTop, ∀ p N (hk:k≤N) (I:Type) [Fintype I] [DecidableEq I]
      (d:I→ℕ) (_:∀ i,d i≤D) (z:I→Site (R.family.side N p))
      (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
      (_:∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
      (s:I→Motion) (c:I→Site (R.family.side k p)),
      (∀ i i':I,i≠i' → (R.family.path.levels.budget k).B^2 <
        separation (point R (z i) (s i) (c i) k) (point R (z i') (s i') (c i') k)) →
      ∀ (names:Census I) (y:(i:I)→Palette R.family (d i)), (∀ i,size (y i)≤β k) →
        filed R d z s c y V r names hk t := by
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
  refine ⟨t+1,dt.trans (Nat.le_succ _),?_⟩
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (D+3) t,
    awake,Many.theta_up (C:=R.family) (max 1 (2*u)) simple] with k late purse gates hot p N hk I _ _ d cap z V r H s c room names y small
  have gate (i:I) : Awake (C:=R.family) R.doors B k (d i) := gates ⟨d i,by have:=cap i;omega⟩
  have wallet (i:I) (j:ℕ) (hj:k≤j) :
      radius R t k j*(span R k j)^(d i+3)*β j^t ≤ 1 := by
    have lower := pow_le_pow_right₀ (span_one R hj) (show d i+3≤D+3 by have:=cap i;omega)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lower (radius_pos R t k j hj).le)
      (pow_nonneg (WardBin.hot _ _).le t)).trans (purse j hj)
  have last := starts N (late.trans hk)
  have seated (i i':I) (hi:i≠i') := room i i' hi
  simp_rw [←parent R _ _ _ (le_refl k) hk] at seated
  have bpos:0<β k:=WardBin.hot A k
  let amp:ℂ:=(↑((β k)⁻¹):ℂ)
  have nrm:‖amp‖=(β k)⁻¹:=by rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr bpos).le]
  let y0 i:=amp • y i
  have norm0 (i:I):size (y0 i)≤1:=by
    rw [size_smul,nrm,inv_mul_le_one₀ bpos]
    exact small i
  have ceil0 (i:I):=WilsonThermometerOwnOffsetInvoice.top R (H i) (y0 i) (norm0 i) up hk
    ⟨last.1,last.2 (d i) (cap i)⟩ (wallet i N hk)
  have lower (i:I) (j:ℕ) (hj:k≤j) (hn:j<N) : 2*radius R t k (j+1)*charge R (r i) (y0 i) hj u≤1:=by
    let X := span R k (j+1)
    let w := radius R t k (j+1)
    let b := β (j+1)
    have hkn := hj.trans j.le_succ
    have warm : max 1 (2*u) ≤ b := hot.trans (grow hkn)
    have fee : 2*u ≤ b^t := ((le_max_right 1 _).trans warm).trans
      (by simpa only [pow_one] using (pow_le_pow_right₀ ((le_max_left 1 _).trans warm) (show 1≤t by omega)))
    have smallcost := adjacent R (H i) (y0 i) (norm0 i) up.le hj hn
    have wpos := (radius_pos R t k (j+1) hkn).le
    calc 2*w*charge R (r i) (y0 i) hj u ≤ 2*w*(X^(d i+3)*u) :=
            mul_le_mul_of_nonneg_left smallcost (by positivity : 0 ≤ 2*w)
         _ = w*X^(d i+3)*(2*u) := by ring
         _ ≤ w*X^(d i+3)*b^t := mul_le_mul_of_nonneg_left fee (mul_nonneg wpos (pow_nonneg (span_pos R k (j+1)).le _))
         _ ≤ 1 := wallet i (j+1) hkn
  apply admitted R d z s c y V r simple hk names seated H gate (fun i=>covered (d i) (cap i))
  · intro i
    have eh:=ceil0 i
    simp only [y0,map_smul,size_smul,nrm] at eh
    rw [radius_succ R t hk]
    convert eh using 1; ring
  · intro i j hj hn
    have eh:=lower i j hj hn
    simp only [y0,charge,map_smul,size_smul,nrm] at eh
    rw [radius_succ R t (hj.trans j.le_succ)]
    unfold charge
    convert eh using 1; ring

end YM.Integration.WilsonThermometerWeakFundedRoster
end
