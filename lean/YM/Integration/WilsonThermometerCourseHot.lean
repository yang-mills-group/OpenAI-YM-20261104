import YM.Integration.WilsonThermometerCourseResidual
import YM.Integration.PhysicalWilsonHotIntegral

/-! The complete physical thermometer on an actual rejected collar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCourseHot
open Filter Finset Set Function MeasureTheory Lattice Wilson RG Source Marker FVA1 OPE.Therm
open Extraction Table Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseResidual Push.AbsoluteSums.Animals
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) {N per i u : ℕ}
local notation "C" => R.family
local notation "ν" k:max => scene R.family.path N per k
local notation "V" k:max => Config G (R.family.side k per)
local notation "ρ" => (R.family.path.levels.clock.forcedAllowance i)

def bare (o : Positions (Fin 3) (R.family.side N per)) (s : (J).Mode) (U : V N) : ℂ :=
  ∏ j ∈ s.val, R.family.O N per (A.station.wheel.atCut (N,per) (index A (grade j)) (vector A univ j))
    (o.origin j) U

private theorem bounded (o : Positions (Fin 3) (R.family.side N per)) (s : (J).Mode) :
    Envelope (bare R A o s) := by
  have continuous : Continuous (bare R A o s) :=
    continuous_finsetProd _ fun j _ => R.family.continuousO N per _ _ (o.origin j)
  exact ⟨continuous.measurable,(isCompact_univ.exists_bound_of_continuousOn
    continuous.continuousOn).imp fun _ cap U => cap U (Set.mem_univ U)⟩

/-- Clip the original complete planted product before its physical conditional.
The residual costs its true doubled cutoff product, including every deposited leg. -/
private theorem cutoff (top : i ≤ N) (old : u ≤ i)
    (o : Positions (Fin 3) (R.family.side N per)) (s : (J).Mode)
    (E : Set (V i)) (meas : MeasurableSet E) (b : ℝ) (pos : 0 < b) :
    let F := bare R A o s
    let T := actualTransport C (N:=N) F top
    (∫ U,‖actualTransport C (N:=N) (E.indicator T) old U‖ ∂ν u) ≤
      b*(ν i).real E + (∫ U,‖F U‖^2 ∂ν N)/b := by
  intro F T
  letI : IsProbabilityMeasure (ν i) := probability R.makes.wilson top
  letI : IsProbabilityMeasure (ν N) := probability R.makes.wilson (le_refl N)
  have eF := bounded R A o s
  change Envelope F at eF
  let B : Set (V N) := {U | ‖F U‖ ≤ b}
  have mb : MeasurableSet B := measurableSet_le eF.meas.norm measurable_const
  let low := B.indicator F
  let tail := fun U => F U-low U
  have meLow : Measurable low := eF.meas.indicator mb
  have lower (U : V N) : ‖low U‖ ≤ b := by
    by_cases hb : U ∈ B
    · simpa only [low,Set.indicator_of_mem hb] using (show ‖F U‖ ≤ b from hb)
    · simp only [low,Set.indicator_of_notMem hb,norm_zero]; exact pos.le
  have eLow : Envelope low := ⟨meLow, b, lower⟩
  have eTail : Envelope tail := by
    obtain ⟨d,cap⟩ := eF.cost
    exact ⟨eF.meas.sub meLow,d+b,fun U =>
      (norm_sub_le (F U) (low U)).trans (add_le_add (cap U) (lower U))⟩
  have ht := ActualWilsonAbsoluteTransport.weighted C R.makes (le_refl N) eF
  have hl := ActualWilsonAbsoluteTransport.weighted C R.makes (le_refl N) eLow
  have hh := ActualWilsonAbsoluteTransport.weighted C R.makes (le_refl N) eTail
  let Y := actualTransport C (N:=N) tail top
  have sub := ActualWilsonAbsoluteTransport.sub C R.makes (le_refl N) ht hl top
  have hard (U : V N) : ‖tail U‖ ≤ ‖F U‖^2 / b := by
    by_cases h : U ∈ B
    · simp only [tail,low,Set.indicator_of_mem h,sub_self,norm_zero]; positivity
    · rw [show tail U=F U from by simp [tail,low,h],le_div_iff₀ pos]
      exact (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (norm_nonneg _)).trans_eq (sq ..).symm
  have near (W : V i) : ‖E.indicator T W‖ ≤ E.indicator (fun _ => b) W + ‖Y W‖ := by
    by_cases h : W ∈ E
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
      have decomp : T W= actualTransport C (N:=N) low top W+Y W := by
        change T W= _+actualTransport C (N:=N) (fun U => F U-low U) top W
        rw [sub]; dsimp only [T]; abel
      exact (decomp ▸ norm_add_le ..).trans (add_le_add_left
        (actualTransport_norm_le C R.makes (le_refl N) lower top W) _)
    · simp only [Set.indicator_of_notMem h,norm_zero,zero_add,norm_nonneg]
  have hT := actualTransport_weighted_integrable_of_integrable C R.makes (le_refl N) ht top
  have raw : Integrable (fun W => ((C).path.rep N per i).eval W • (E.indicator T) W) (prior G _) := by
    apply (hT.indicator meas).congr (ae_of_all _ fun W => ?_)
    by_cases h : W∈E <;> simp [h,T]
  have slice := actualScene_integrable_of_weighted C R.makes top raw
  have iy := (actualScene_integrable_of_weighted C R.makes top
    (actualTransport_weighted_integrable_of_integrable C R.makes (le_refl N) hh top)).norm
  have it := (actualScene_integrable_of_weighted C R.makes (le_refl N) hh).norm
  obtain ⟨d,dc⟩ := eF.cost
  have squares : Integrable (fun U : V N => ‖F U‖^2) (ν N) := by
    apply Integrable.of_bound (eF.meas.norm.pow_const 2).aestronglyMeasurable (d^2)
    exact ae_of_all _ fun U => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (dc U) 2
  have big : (∫ W,‖Y W‖ ∂ν i) ≤ (∫ U,‖F U‖^2 ∂ν N)/b := calc
    _ ≤ ∫ U,‖tail U‖ ∂ν N := ActualWilsonAbsoluteTransport.first C R.makes (le_refl N) hh top
    _ ≤ ∫ U,‖F U‖^2 / b ∂ν N := integral_mono it (squares.div_const b) hard
    _ = _ := integral_div .. 
  have ib : Integrable (E.indicator (fun _ : V i => b)) (ν i) := (integrable_const _).indicator meas
  calc
    _ ≤ ∫ W,‖E.indicator T W‖ ∂ν i := ActualWilsonAbsoluteTransport.first C R.makes top raw old
    _ ≤ ∫ W,E.indicator (fun _ => b) W + ‖Y W‖ ∂ν i := integral_mono slice.norm (ib.add iy) near
    _ = b*(ν i).real E + ∫ W,‖Y W‖ ∂ν i := by
      rw [integral_add ib iy,integral_indicator meas,setIntegral_const]; simp [smul_eq_mul,mul_comm,Y]
    _ ≤ _ := add_le_add_right big _

/-- At every measured age a physical failed collar may be charged against the
complete submitted face at any earlier date. The product's second moment is
always on the original cutoff with its own three microscopic positions. -/
theorem ordered (simple : G.Simple) (clock : Poetry R.family.path.levels) {c : ℝ}
    (c0 : 0 < c) (q : ℕ) : ∀ᶠ i : ℕ in atTop, ∀ (A : Group R.family 6) {N per u : ℕ} (top : i ≤ N)
    (old : u ≤ i) (o : Positions (Fin 3) (R.family.side N per))
    (_ref : ∀ j : Fin 3, R.family.ref (grade j) ≤ N) (s : (J).Mode)
    (X : Support (R.family.side i per)) (E : Set (Config G (R.family.side i per))),
    MeasurableSet E → E ⊆ SelectedCofactorAnchoredRegister.hot (c*(R.family.path.rep N per i).p.threshold) X →
    let κ := R.family.path.levels.clock.forcedAllowance i
    let F := bare R A o s
    let T := fun W => (table R A simple top o W).part s
    (∫ W, ‖actualTransport C (N:=N) (E.indicator T) old W‖ ∂scene (C).path N per u) ≤
      κ^q*((X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) +
        ∫ U,‖F U‖^2 ∂scene (C).path N per N) := by
  filter_upwards [PhysicalWilsonHotIntegral.sites R simple clock c0 (2*q)] with i quoted
  intro A N per u top old o ref s X E meas atRoot κ F T
  let μ := scene (C).path N per i
  letI : IsProbabilityMeasure μ := probability R.makes.wilson top
  let D : ℝ := (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ)
  have k0 : 0 < κ := Real.exp_pos _
  have kp := pow_pos k0 q
  have rare : μ.real E ≤ D*κ^(2*q) :=
    (measureReal_mono atRoot (measure_ne_top _ _)).trans (quoted N top per X)
  have same : T=actualTransport C (N:=N) F top := funext fun W => observed R A simple top o ref W s
  rw [same]
  calc
    _ ≤ (κ^q)⁻¹*μ.real E + (∫ U,‖F U‖^2 ∂scene (C).path N per N)/(κ^q)⁻¹ :=
      cutoff R A top old o s E meas _ (inv_pos.mpr kp)
    _ ≤ (κ^q)⁻¹*(D*κ^(2*q)) + (∫ U,‖F U‖^2 ∂scene (C).path N per N)/(κ^q)⁻¹ :=
      add_le_add_left (mul_le_mul_of_nonneg_left rare (inv_nonneg.mpr kp.le)) _
    _ = _ := by rw [two_mul,pow_add]; field_simp; ring

theorem original (simple : G.Simple) (clock : Poetry R.family.path.levels) {c : ℝ}
    (c0 : 0 < c) (q : ℕ) : ∀ᶠ i : ℕ in atTop, ∀ {N per u : ℕ} (top : i ≤ N)
    (old : u ≤ i) (o : Positions (Fin 3) (R.family.side N per))
    (_ref : ∀ j : Fin 3, R.family.ref (grade j) ≤ N) (s : (J).Mode)
    (X : Support (R.family.side i per)) (E : Set (Config G (R.family.side i per))),
    MeasurableSet E → E ⊆ SelectedCofactorAnchoredRegister.hot (c*(R.family.path.rep N per i).p.threshold) X →
    let κ := R.family.path.levels.clock.forcedAllowance i
    let F := bare R A o s
    let T := fun W => (table R A simple top o W).part s
    (∫ W, ‖actualTransport C (N:=N) (E.indicator T) old W‖ ∂scene (C).path N per u) ≤
      κ^q*((X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) +
        ∫ U,‖F U‖^2 ∂scene (C).path N per N) := by
  filter_upwards [ordered R simple clock c0 q] with i all
  exact all A

/-- The true squared field and support count are charged before the two
regulators. The physical report recovers its seven coupling powers and may
restore any fixed number of native hard divisors on precisely this collar. -/
theorem paid_on_run (simple : G.Simple) (clock : Poetry R.family.path.levels)
    {c K ε : ℝ} (c0 : 0 < c) (k0 : 0 ≤ K) (ep : 0 < ε) (debt bills : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ (A : Group R.family 6) {N per u m : ℕ} (top : i ≤ N) (old : u ≤ i)
      (_since : m ≤ i) (o : Positions (Fin 3) (R.family.side N per))
      (_ref : ∀ j : Fin 3, R.family.ref (grade j) ≤ N) (s : (J).Mode)
      (X : Support (R.family.side i per)) (E : Set (Config G (R.family.side i per))),
      MeasurableSet E → E ⊆ SelectedCofactorAnchoredRegister.hot (c*(R.family.path.rep N per i).p.threshold) X →
      let g := Pert.Asymptotics.regulatorRun C N per i
      let a := Pert.Asymptotics.regulatorRun C N per m
      let κ := R.family.path.levels.clock.forcedAllowance i
      let F := bare R A o s
      let T := fun W => (table R A simple top o W).part s
      (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) + (∫ U,‖F U‖^2 ∂scene (C).path N per N) ≤ K/g^debt →
      a^7*((∫ W,‖actualTransport C (N:=N) (E.indicator T) old W‖ ∂scene (C).path N per u)/κ^bills)
        ≤ 4*ε*a^9 := by
  let δ := ε/(K+1)
  have den : 0 < K+1 := by linarith only [k0]
  have dp : 0 < δ := div_pos ep den
  have cost : δ*K ≤ ε := calc
    _ ≤ δ*(K+1) := mul_le_mul_of_nonneg_left (by linarith) dp.le
    _ = _ := by dsimp [δ]; field_simp
  filter_upwards [ordered R simple clock c0 (bills+1),
    OriginalForcedFlat.allowance R simple (debt+2) dp] with i heard flat
  intro A N per u m top old since o ref s X E meas hot g a κ F T gross
  have gp : 0 < g := ActualRunKernelPackets.regulator_pos R N per i top
  have ap : 0 < a := ActualRunKernelPackets.regulator_pos R N per m (since.trans top)
  have band : g ≤ 2*a := WilsonLocalCompactRichPortUnits.compared R simple since top per
  have kp : 0 < κ := Real.exp_pos _
  have head : 0 ≤ (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) + (∫ U,‖F U‖^2 ∂scene (C).path N per N : ℝ) :=
    add_nonneg (Nat.cast_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have returned := heard A top old o ref s X E meas hot
  let total := ∫ W,‖actualTransport C (N:=N) (E.indicator T) old W‖ ∂scene (C).path N per u
  have divided : total/κ^bills ≤ κ*((X.card*ballCost 2*Fintype.card PlaqAxes : ℕ)+(∫ U,‖F U‖^2 ∂scene (C).path N per N)) := by
    apply (div_le_iff₀ (pow_pos kp _)).mpr
    dsimp only at returned
    exact returned.trans_eq (by dsimp only [κ,F]; rw [pow_succ]; ring)
  calc
    _ ≤ a^7*(δ*g^(debt+2)*(K/g^debt)) :=
      mul_le_mul_of_nonneg_left (divided.trans (mul_le_mul (flat N per top) gross head (by positivity))) (pow_nonneg ap.le _)
    _ = a^7*((δ*K)*g^2) := by rw [pow_add]; field_simp
    _ ≤ a^7*(ε*(2*a)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul cost (pow_le_pow_left₀ gp.le band 2) (sq_nonneg _) ep.le) (pow_nonneg ap.le _)
    _ = _ := by ring

theorem paid (simple : G.Simple) (clock : Poetry R.family.path.levels)
    {c K ε : ℝ} (c0 : 0 < c) (k0 : 0 ≤ K) (ep : 0 < ε) (debt bills : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ {N per u m : ℕ} (top : i ≤ N) (old : u ≤ i)
      (_since : m ≤ i) (o : Positions (Fin 3) (R.family.side N per))
      (_ref : ∀ j : Fin 3, R.family.ref (grade j) ≤ N) (s : (J).Mode)
      (X : Support (R.family.side i per)) (E : Set (Config G (R.family.side i per))),
      MeasurableSet E → E ⊆ SelectedCofactorAnchoredRegister.hot (c*(R.family.path.rep N per i).p.threshold) X →
      let g := Pert.Asymptotics.regulatorRun C N per i
      let a := Pert.Asymptotics.regulatorRun C N per m
      let κ := R.family.path.levels.clock.forcedAllowance i
      let F := bare R A o s
      let T := fun W => (table R A simple top o W).part s
      (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) + (∫ U,‖F U‖^2 ∂scene (C).path N per N) ≤ K/g^debt →
      a^7*((∫ W,‖actualTransport C (N:=N) (E.indicator T) old W‖ ∂scene (C).path N per u)/κ^bills)
        ≤ 4*ε*a^9 := by
  filter_upwards [paid_on_run R simple clock c0 k0 ep debt bills] with i all
  exact all A

end YM.Integration.WilsonThermometerCourseHot
end
