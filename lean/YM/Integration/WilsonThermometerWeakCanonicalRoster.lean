import YM.Integration.WilsonThermometerWeakCanonicalAllowance

/-! The original reflected joint is funded at its fully restored source amplitudes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCanonicalRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerReflectedTrajectory
open scoped Classical Topology
open WilsonThermometerReflectedRoster WilsonThermometerWeakCanonicalAllowance
open Next.Rank Next.Rank.Perch Next.Rank.Tapes Next.Rank.Atlas
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {N p k:ℕ} {I:Type}
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "β" => R.alloy.B.a.clock.hatBeta

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) {H0:ℕ} (panel:Panel H0) :
    ∀ᶠ k:ℕ in atTop, ∀ p N (hk:k≤N) (I:Type) [Fintype I] [DecidableEq I]
      (d:I→ℕ) (_:∀ i,d i≤D) (z:I→Site (R.family.side N p))
      (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
      (_:∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
      (s:I→Motion) (c:I→Site (R.family.side k p)),
      (∀ i i':I,i≠i' → (R.family.path.levels.budget k).B^2 <
        separation (point R (z i) (s i) (c i) k) (point R (z i') (s i') (c i') k)) →
      ∀ (names:Census I) (y:(i:I)→Palette R.family (d i)), (∀ i,size (y i)≤Perch.bill ((panel.bag ((A).clock.J k)).credit-1) (clim (A) k)) →
        filed R d z s c y V r names hk (maximum G D+1) := by
  choose a pos caps using fun e : Fin (D+1)=>Cap.cost (line (primaryLetter e.val)) (e.val+2)
  let u : ℝ := 1+∑ e,a e
  have nonneg : 0≤∑ e,a e := Finset.sum_nonneg (fun e _=>(pos e).le)
  have up : 0<u := by dsimp [u];linarith
  have covered (e:ℕ) (he:e≤D) : Cap (e+2) (line (primaryLetter e)) u := by
    let l : Fin (D+1) := ⟨e,by omega⟩
    have c := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(pos j).le) (Finset.mem_univ l)
    exact (caps l).increase (by dsimp [u];linarith)
  let e (j:Fin (D+1)):=pulseFee j.val*u*(Fintype.card (Letter j.val):ℝ)
  have en (j:Fin (D+1)):0≤e j:=mul_nonneg (mul_nonneg (feepos j.val).le up.le) (by positivity)
  let c:=1+2*u+∑ j,e j
  have ct:2*u≤c:=by dsimp only [c];linarith only [Finset.sum_nonneg (s:=Finset.univ) (fun j _=>en j)]
  have co:0<c:=lt_of_lt_of_le (by linarith only [up]) ct
  have each (j:Fin (D+1)):e j≤c:=by
    have h:=Finset.single_le_sum (fun i (_:i∈Finset.univ)=>en i) (Finset.mem_univ j)
    dsimp only [c];linarith only [h,up]
  let t:=maximum G D+1
  obtain ⟨_,_,starts⟩:=Many.startPay (C:=R.family) simple D u up
  obtain ⟨k₀,starts⟩:=eventually_atTop.mp starts
  have awake : ∀ᶠ k:ℕ in atTop,∀ e:Fin (D+1),Awake (C:=R.family) R.doors B k e.val :=
    Filter.eventually_all.mpr fun e=>(WilsonThermometerOffsetLedger.original R simple shop e.val).mono fun _ h=>h.1
  have grow := Many.beta_le' (C:=R.family) simple
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (D+3) t,
    awake,Many.theta_up (C:=R.family) 1 simple,restored R simple panel co.le] with k late purse gates hot bill p N hk I _ _ d cap z V r H s c0 room names y small
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
  let scale:=β k/c
  have so:0<scale:=div_pos bpos co
  have full:scale*c=β k:=div_mul_cancel₀ _ co.ne'
  let amp:ℂ:=(↑scale⁻¹:ℂ)
  have nrm:‖amp‖=scale⁻¹:=by rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr so).le]
  let y0 i:=amp • y i
  have norm0 (i:I):size (y0 i)≤1:=by
    rw [size_smul,nrm,inv_mul_le_one₀ so]
    exact (small i).trans ((le_div_iff₀ co).mpr (by rwa [mul_comm c] at bill))
  have paid (i:I):pricesTop (fly A) (far A) N (d i)*(scale*u)≤far A N*(β N)^t:=by
    apply WilsonThermometerWeakCanonicalAllowance.source R (cap i) (hot.trans (grow hk)) last.1 up.le so.le
    calc
      _ ≤ scale*c:=mul_le_mul_of_nonneg_left (each ⟨d i,by have:=cap i;omega⟩) so.le
      _ ≤ β N:=full.le.trans (grow hk)
  apply admitted R d z s c0 y V r simple hk names seated H gate (fun i=>covered (d i) (cap i))
  · intro i
    have eh:=WilsonThermometerOwnOffsetInvoice.top R (H i) (y0 i) (norm0 i) (mul_pos so up) hk ⟨last.1,paid i⟩ (wallet i N hk)
    simp only [y0,map_smul,size_smul,nrm] at eh
    convert eh using 1
    field_simp [so.ne'];ring
  · intro i j hj hn
    let X:=span R k (j+1)
    let w:=radius R t k (j+1)
    let b:=β (j+1)
    have hk':=hj.trans j.le_succ
    have b1:1≤b:=hot.trans (grow hk')
    have load:2*(scale*u)≤b^t:=by
      calc
        _ = scale*(2*u):=by ring
        _ ≤ scale*c:=mul_le_mul_of_nonneg_left ct so.le
        _ = β k:=full
        _ ≤ b:=grow hk'
        _ ≤ b^t:=by simpa only [pow_one] using (pow_le_pow_right₀ b1 (show 1≤t by dsimp only [t];omega))
    have smallcost:=WilsonThermometerOwnOffsetInvoice.adjacent R (H i) (y0 i) (norm0 i) (mul_nonneg so.le up.le) hj hn
    have same:charge R (r i) (y i) hj u=charge R (r i) (y0 i) hj (scale*u):=by
      simp only [charge,y0,map_smul,size_smul,nrm];field_simp [so.ne']
    rw [same]
    have wp:0≤w:=(radius_pos R t k (j+1) hk').le
    calc
      _ ≤ 2*w*(X^(d i+3)*(scale*u)):=mul_le_mul_of_nonneg_left smallcost (by positivity)
      _ = w*X^(d i+3)*(2*(scale*u)):=by ring
      _ ≤ w*X^(d i+3)*b^t:=mul_le_mul_of_nonneg_left load (mul_nonneg wp (pow_nonneg (span_pos R k (j+1)).le _))
      _ ≤ 1:=wallet i (j+1) hk'

end YM.Integration.WilsonThermometerWeakCanonicalRoster
end
