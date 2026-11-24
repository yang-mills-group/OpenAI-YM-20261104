import YM.Integration.WilsonPositionRawMesh
import YM.Integration.WilsonPositionGradedThermometerHearing
import YM.Integration.WilsonPositionThermometerSevenFaceRate

/-! Quantitative entrance from the true Wilson source and its simultaneously
measured detector, at their original finite cutoffs, to the finite auxiliary
position estimate. The physical UV and volume limits stay on the same Bliss. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawCutoff
open Filter Function Finset Set Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb RG17 Trace.Pilot PhysMS PhysicalNext.Repeat.Legato
open WilsonPositionRawMesh WilsonPositionSeparatedProfileMatching
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)

include H in
theorem uniform : ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ i : ℕ in atTop,
    slope Z (Z.run.step i) q d φ v ≤ A ∧
    price Z (Z.run.step i) q d φ v ≤ A * (1+mass Z (Z.run.step i) q)^q := by
  let b (k : Fin (q+1)) := 1+‖Scale.System.Readout Z.scheme Z.criterion T 0 d k n φ v‖
  have limits (k : Fin (q+1)) : ∀ᶠ i : ℕ in atTop, ‖source Z (Z.run.step i) q d φ v k‖ ≤ b k :=
    ((H.wilsonLimit 0 n d k v φ).norm.eventually_lt_const (by dsimp [b]; linarith)).mono fun _ hi => hi.le
  let total := ∑ k, b k
  have pos : 0 ≤ total := sum_nonneg fun k _=>by dsimp [b]; positivity
  have qr : (1:ℝ) ≤ q+1 := by linarith [Nat.cast_nonneg (α:=ℝ) q]
  refine ⟨(1+total)*(q+1),one_le_mul_of_one_le_of_one_le (by linarith) qr,?_⟩
  filter_upwards [eventually_all.mpr limits] with i within
  have roots : 0 ≤ mass Z (Z.run.step i) q := sum_nonneg fun _ _=>abs_nonneg _
  have rate : ∀ s : Fin (q+1), (s:ℝ) ≤ q+1 := fun s => by exact_mod_cast s.isLt.le
  have toll : ∀ s : Fin (q+1), mass Z (Z.run.step i) q^(s:ℕ) ≤ (1+mass Z (Z.run.step i) q)^q := fun s=>
    (pow_le_pow_left₀ roots (by linarith) s.val).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have funded : total ≤ (1+total)*(q+1) :=
    le_trans (by linarith : total ≤ 1+total) (le_mul_of_one_le_right (by linarith) qr)
  constructor
  · calc
      _ ≤ total*(q+1) := by
        rw [WilsonPositionRawMesh.slope,show total*(q+1)=∑ k,b k*(q+1) by dsimp [total];rw [sum_mul]]
        exact sum_le_sum fun k _=>mul_le_mul (within k) (rate k) (by positivity) (by dsimp [b];positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · calc
      _ ≤ total * (1+mass Z (Z.run.step i) q)^q := by
        rw [price,show total * (1+mass Z (Z.run.step i) q)^q=∑ k,b k*(1+mass Z (Z.run.step i) q)^q by dsimp [total];rw [sum_mul]]
        exact sum_le_sum fun k _=>mul_le_mul (within k) (toll k) (pow_nonneg roots _) (by dsimp [b]; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right funded (by positivity)

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (J : ℝ → tower S)
    {l : Ultrafilter (ℕ × ℕ)} {Y : (Bel R.family.book).Hierarchy} {B : ℕ}
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) hG (B:=B)
local notation "seen" => observed Z F J none d φ v

def thermometer (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6) (r : ℝ) (z : ℕ × ℕ) : ℝ :=
  (WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A r z).re /
    Rose.cT Z.criterion.cut G Z.criterion.image

theorem measured (lead : Leading F J) (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (simple : G.Simple) (prior : (l : Filter _) ≤ f.fuse) :
    ∀ᶠ r in trail, Tendsto (thermometer Z F J A r) (l : Filter _) (𝓝 (θ r)) := by
  filter_upwards [WilsonPositionGradedThermometerHearing.signed F J Z.store lead Z.criterion A book simple prior] with r h
  exact (Complex.continuous_re.continuousAt.tendsto.comp h).div_const _

include H in
theorem on_axis (axis : ℕ → ℝ → (ℕ × ℕ) → ℝ) (lead : Leading F J) (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J) (prior : (l : Filter _) ≤ f.fuse)
    (coupled : Coupling G θ) (panel : ℝ → (ℕ × ℕ) → ℂ)
    (reports : ∀ᶠ r in trail, Tendsto (panel r) (l : Filter _) (𝓝 (seen r)))
    (paid : ∀ δ > 0, ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
      ∀ᶠ z : ℕ × ℕ in (l : Filter _),
        |axis i r z| ≤ 1 ∧ |forward Z (Z.run.step i) q (axis i r z)| ≤ 1 ∧
        ‖panel r z - raw Z (Z.run.step i) q d φ v (axis i r z)‖ ≤ δ*|θ r|^q ∧
        |thermometer Z F J A r z-forward Z (Z.run.step i) q (axis i r z)| ≤ δ*|θ r|^q ∧
        (1+mass Z (Z.run.step i) q)^q*|axis i r z|^(q+1) ≤ δ*|θ r|^q) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v q := by
  obtain ⟨C,pos,late⟩ := uniform Z H d φ v q
  obtain ⟨N,hn⟩ := eventually_atTop.mp late
  have zero := coupled.conforms hG
  have enough := (WilsonPositionAuxiliaryMesh.grows Z.run q trail coupled.positive zero).eventually_ge_atTop N
  intro ε he
  let δ := ε/(3+3*C)
  have hp : 0 < δ := div_pos he (by linarith)
  have cap : (3+3*C)*δ = ε := by dsimp [δ]; field_simp
  have tight : ∀ᶠ r in trail, |θ r| ≤ 1 := (zero.abs.eventually_lt_const (by simp)).mono fun _ h=>h.le
  filter_upwards [enough,paid δ hp, reports, measured Z F J lead A book hG prior,coupled.positive,tight]
    with r morning offer live read positive small
  obtain ⟨i,ready,issued⟩ := offer
  let t := |θ r|^q
  have tp : 0 < t := pow_pos (abs_pos.mpr positive.ne') _
  have benefit := mul_pos hp tp
  have left := Metric.tendsto_nhds.mp live _ benefit
  have meter := Metric.tendsto_nhds.mp read _ benefit
  obtain ⟨z,pulse,form,valid⟩ := (left.and (meter.and issued)).exists
  obtain ⟨gx,cut,sourceCost,meterCost,changeCost⟩ := valid
  obtain ⟨bound,largest⟩ := hn i (morning.trans ready)
  refine ⟨i,ready,?_⟩
  have back : |θ r-forward Z (Z.run.step i) q (axis i r z)| ≤ 2*δ*t := by
    calc
      _ ≤ |θ r-thermometer Z F J A r z| + |thermometer Z F J A r z-forward Z (Z.run.step i) q (axis i r z)| := abs_sub_le ..
      _ ≤ _ := by rw [abs_sub_comm,← Real.dist_eq]; linarith
  have result := finite_change Z (Z.run.step i) q d φ v (axis i r z) (θ r) gx small cut
  have measuredCost : _ ≤ C*(2*δ*t) + C*(δ*t) :=
    result.trans (add_le_add (mul_le_mul bound back (abs_nonneg _) (by linarith))
      ((mul_le_mul_of_nonneg_right largest (pow_nonneg (abs_nonneg _) _)).trans
        (by rw [mul_assoc];exact mul_le_mul_of_nonneg_left changeCost (by linarith))))
  have balance := norm_sub_le_norm_sub_add_norm_sub (seen r) (panel r z) (WilsonPositionFiniteMSBank.finite Z (Z.run.step i) d φ v q (θ r))
  have rest := norm_sub_le_norm_sub_add_norm_sub (panel r z) (raw Z (Z.run.step i) q d φ v (axis i r z))
    (WilsonPositionFiniteMSBank.finite Z (Z.run.step i) d φ v q (θ r))
  rw [dist_eq_norm,norm_sub_rev] at pulse
  rw [norm_sub_rev] at measuredCost
  rw [←cap]
  exact balance.trans ((add_le_add pulse.le (rest.trans (add_le_add sourceCost measuredCost))).trans (by
    change δ*t + (δ*t+(C*(2*δ*t)+C*(δ*t))) ≤ (3+3*C)*δ*t
    nlinarith only [benefit.le]))

include H in
theorem booked (lead : Leading F J) (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J) (prior : (l : Filter _) ≤ f.fuse)
    (coupled : Coupling G θ) (panel : ℝ → (ℕ × ℕ) → ℂ)
    (reports : ∀ᶠ r in trail, Tendsto (panel r) (l : Filter _) (𝓝 (seen r)))
    (paid : ∀ δ > 0, ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
      ∀ᶠ z : ℕ × ℕ in (l : Filter _),
        |g r z| ≤ 1 ∧ |forward Z (Z.run.step i) q (g r z)| ≤ 1 ∧
        ‖panel r z - raw Z (Z.run.step i) q d φ v (g r z)‖ ≤ δ*|θ r|^q ∧
        |thermometer Z F J A r z-forward Z (Z.run.step i) q (g r z)| ≤ δ*|θ r|^q ∧
        (1+mass Z (Z.run.step i) q)^q*|g r z|^(q+1) ≤ δ*|θ r|^q) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v q :=
  on_axis Z H d φ v q F J (fun _ => g) lead A book prior coupled panel reports paid

end YM.Integration.WilsonPositionRawCutoff
