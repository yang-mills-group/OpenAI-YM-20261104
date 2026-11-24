import YM.Integration.WilsonAddressedWeakMaxwellPositions
import YM.Integration.WilsonAddressedWeakStationRoom

/-! The original two-point target on every actual submitted fine placement of a fixed generic detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFiledTargets
open Function Filter Set MeasureTheory Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open Next.Rank Next.Rank.Station Next.Rank.Read
open WilsonAddressedWeakCalibration WilsonAddressedWeakPackedCertificate
open Metric
open WilsonAddressedWeakCalibration WilsonAddressedWeakMaxwellPositions
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "A!"=>R.family.path.levels
set_option quotPrecheck false

theorem fits (simple:G.Simple) (φ:Test 2) (genericShape:tsupport φ ⊆ generic 2)
    (b:ℝ) (hb:0<b) :
    ∀ᶠ k:ℕ in atTop, Station.Allowed (A!) b k → ∀ (N p:ℕ) (live:k≤N)
      (x:Points 2), x∈tsupport φ →
        Station.Fit (A!) b k (projected R (p:=p) live (Station.gap (A!) b k) (gap_pos ..) x) := by
  obtain ⟨c,cp,clear⟩:= φ.hasCompactSupport.exists_cthickening_subset_open (genericOpen 2) genericShape
  obtain ⟨M,bounded⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  have shrink : Tendsto (fun k => (16:ℝ)*(Station.mag (A!) b k)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (mag_rate (A!) simple hb)).const_mul 16
  have cost := shrink.eventually (gt_mem_nhds (lt_min cp zero_lt_one))
  have heat : Tendsto (fun k => ((A!).clock.monitor k)^2) atTop atTop := by
    have h := mag_rate (A!) simple (b:=1) (by norm_num)
    change Tendsto (fun k=>(A!).clock.monitor k^(1:ℝ)) atTop atTop at h
    simpa only [Real.rpow_one,Function.comp_def] using ((tendsto_pow_atTop (n:=2) (by norm_num)).comp h)
  filter_upwards [cost,heat.eventually (eventually_ge_atTop (8*(M+1)))] with k small large
  intro allowed N p live x supported
  let ρ:=gap (A!) b k
  let v:=projected R (p:=p) live ρ (gap_pos ..) x
  have exactSites := (stations R (p:=p) live b x).2.2
  have actualDist : dist v x ≤ 16*(mag (A!) b k)⁻¹ := by
    have distance := (actual R (p:=p) live ρ (gap_pos ..) x).2
    have mesh : R.family.S.a k/ρ=(mag (A!) b k)⁻¹ := by
      dsimp [ρ,gap]; field_simp [(A!).S.a_pos k |>.ne', (mag_pos (A!) b k).ne']
    simpa only [mesh] using distance
  have vg : v ∈ generic 2 := clear (mem_cthickening_of_dist_le v x c (tsupport φ) supported
    ((actualDist.trans small.le).trans (min_le_left ..)))
  have vsize : ‖v‖ ≤ M+1 := by
    have dif := norm_sub_norm_le v x
    rw [←dist_eq_norm] at dif
    linarith only [dif,actualDist.trans ((le_of_lt small).trans (min_le_right ..)),bounded x supported]
  have key : Station.key (A!) b k v=ρ • v := (anchored (A!) b k v).trans (by rw [exactSites])
  constructor
  · rw [key]
    intro j i l equal
    apply vg j
    change ρ*(v i j)=ρ*(v l j) at equal
    exact mul_left_cancel₀ (gap_pos ..).ne' equal
  · intro i j
    rw [key]
    change |ρ*(v i j)| ≤ _
    rw [abs_mul,abs_of_pos (gap_pos ..)]
    have item : |v i j|≤M+1 :=
      ((by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) j : |v i j|≤‖v i‖).trans
        (PiLp.norm_apply_le v i)).trans vsize
    have head : 8*|v i j| ≤ (A!).clock.monitor k^2 :=
      (mul_le_mul_of_nonneg_left item (by norm_num)).trans large
    have geometry := (le_div_iff₀ ((A!).S.a_pos k)).mp allowed.dilation
    have weight := mul_le_mul_of_nonneg_left head (gap_pos (A!) b k).le
    dsimp [gap,ρ] at weight ⊢
    linarith only [weight,geometry]

theorem targets {k N p d:ℕ} {B:Local.Physical.Deck G} (b:ℝ) (mark:Fin 2→Glyph B d)
    (live:k≤N) (x:Points 2) :
    let v:=projected R (p:=p) live (gap (A!) b k) (gap_pos ..) x
    ∀ fit:Station.Fit (A!) b k v, ∃ good:v∈conf 2,
      Ship.targets R.family (WilsonAddressedWeakMaxwellPositions.tags R B mark) fit =
        Read.cumulants R.family v (WilsonAddressedWeakMaxwellPositions.tags R B mark) good := by
  intro v fit
  have eq : Station.tested (A!) b k v=v := (stations R (p:=p) live b x).2.2
  have native : Station.tested (A!) b k v∈conf 2 := Ship.fitting fit
  have good : v∈conf 2 := eq ▸ native
  let tags:=WilsonAddressedWeakMaxwellPositions.tags R B mark
  have move (y z:Points 2) (ident:y=z) (atY:y∈conf 2) (atZ:z∈conf 2) :
      Read.cumulants R.family y tags atY=Read.cumulants R.family z tags atZ := by subst z; rfl
  exact ⟨good,move _ _ eq native good⟩

end YM.Integration.WilsonAddressedWeakFiledTargets
