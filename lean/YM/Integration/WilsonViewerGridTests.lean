import YM.Integration.WilsonViewerMixedPositions
import YM.Integration.WilsonViewerGridPins
import YM.Integration.WilsonThermometerWeakAllViewSeries
import YM.Integration.WilsonPositionProgramPhysicalCells

/-! Position interpolation on the original homogeneous fields and the finite
MS bank. The same screened node error buys the full ball of joint tests. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot Lattice
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open WilsonThermometerWeakValueRecovery WilsonThermometerWeakProbeTest WilsonThermometerWeakCoefficientTail WilsonThermometerWeakMeasuredSeries
open WilsonPositionHomogeneousFrame WilsonViewerReportingGrid WilsonViewerAlignedResidual
open private smooth from YM.Integration.WilsonPositionProgramPhysicalCells
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} (ms : Main.Match Z simple M σ branch) (ν : ℝ) {n H : ℕ} {d : Caps n}
    (v : MaxwellSlots R.family d) (within : ∀ i, d i≤H)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z
local notation "c" => coefficient Z M ν H (commonCaps v within)

include ms in
/-- The separately prescribed finite response is smooth through every spatial
order on the separated domain. This uses the normalized fixed-frame Wick response. -/
theorem ms_regular (d : ℕ) (z : Fin n → Sec G d) (i : ℕ) :
    ContDiffOn ℝ ∞ (coefficient Z M ν d z i) (conf n) := by
  apply ContDiffOn.congr (f:=WilsonPositionProgramPhysicalCells.point Z (M:=M) ν z i)
  · exact fun x hx=>(smooth Z ν z i x hx).contDiffWithinAt
  · intro x hx
    simp only [coefficient,WilsonPositionSeparatedProfileMatching.extended,dif_pos hx]
    rw [WilsonPositionHomogeneousComparison.filed Z M ms ν d ⟨x,hx⟩ z i]
    exact (WilsonPositionProgramFixedFrame.output Z ms ν z i ⟨x,hx⟩).symm

private theorem testMass (K:Set (Points n)) (compact:IsCompact K) (φ:Test n)
    (inside:tsupport (φ:Points n→ℂ)⊆K) (w:ℝ) (cash:Charges φ 0 w) :
    (∫x,‖φ x‖)≤volume.real K*w := by
  letI : IsFiniteMeasure (volume.restrict K):=isFiniteMeasure_restrict.mpr (compact.measure_lt_top (μ:=volume)).ne
  calc
    _ = ∫x in K,‖φ x‖ := (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx=>by
      rw [image_eq_zero_of_notMem_tsupport (fun hy=>hx (inside hy)),norm_zero]).symm
    _ ≤ ∫_x in K,w := by
      apply integral_mono_ae (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.integrableOn (integrable_const w)
      exact ae_of_all _ fun x=>by simpa only [norm_iteratedFDeriv_zero] using cash 0 le_rfl x
    _ = _ := by rw [setIntegral_const,smul_eq_mul]

theorem compact_signed {g:ℝ→ℝ} {F₀:ℝ→Points n→ℂ} {p:ℕ} (positive:∀ᶠr in trail,0<g r)
    (estimate:∀ K, IsCompact K → K⊆conf n → ∃ C,0≤C ∧ ∀ᶠr in trail,∀x∈K,‖F₀ r x‖≤C*(g r)^p) :
    WilsonThermometerWeakValueRecovery.Signed trail (conf n) F₀ g p 0 := by
  intro K compact clear
  obtain ⟨C,cp,rows⟩:=estimate K compact clear
  refine ⟨volume.real K*C, mul_nonneg measureReal_nonneg cp,?_⟩
  filter_upwards [rows,positive] with r good gp φ support w _ cash
  have variation:=WilsonThermometerWeakAllViewSeries.applied φ support (F₀ r) (C*(g r)^p) good
  exact variation.trans ((mul_le_mul_of_nonneg_right (testMass K compact φ support w cash) (mul_nonneg cp (pow_nonneg gp.le _))).trans_eq (by ring))

include run ms in
theorem Selected.grid_tests (Γ:Grid (ℓ:=ℓ) F H θ) (W:Finset E4) (p q:ℕ) (temperature:Coupling G θ)
    (nodes:Nodes R.family.S W Γ.date (fun r=>measured F none (pub r) v r-approximate c q (θ r)) θ p) :
    WilsonThermometerWeakValueRecovery.Signed trail (conf n) (fun r=>measured F none (pub r) v r-approximate c q (θ r)) θ p 0 := by
  let T:=fun r=>measured F none (pub r) v r
  let A:=fun r=>approximate c q (θ r)
  have legal:=ms_regular Z M ms ν H (commonCaps v within)
  have st : ∀ᶠ r in trail, ContDiffOn ℝ ∞ (T r) (conf n) := RG17.positiveLength.mono
    fun r hr=>WilsonThermometerWeakMeasuredBounds.unselected F pub v r hr
  have sa (r):ContDiffOn ℝ ∞ (A r) (conf n):=WilsonThermometerWeakCoefficientTail.smooth c _ _ fun a _=>legal a
  have decay:=Coupling.conforms simple temperature
  have positive:=temperature.positive
  have flat (k:ℕ):Bounded trail (conf n) (fun r=>T r-A r) k:=by
    have finite:=WilsonThermometerWeakCoefficientTail.original (conf_open n) c (Finset.range (q+1)) θ k 0
      (fun a _=>legal a) (fun a _=>Nat.zero_le a) decay (positive.mono fun _ h=>h.le)
    intro K compact clear
    obtain ⟨U,Un,free⟩:=WilsonThermometerWeakMeasuredBounds.maxwell v K compact clear k
    obtain ⟨V,Vn,printed⟩:=finite K compact clear
    have close:=WilsonPositionHomogeneousLeading.jets F J Z run.leading run.obeys simple d v k compact clear zero_lt_one
    refine ⟨1+U+V,by positivity,?_⟩
    filter_upwards [close,printed,st] with r paid right t x hx
    have left:‖iteratedFDeriv ℝ k (T r) x‖≤1+U:=(norm_le_norm_sub_add _ (iteratedFDeriv ℝ k (WickGoal v) x)).trans (add_le_add (paid x hx) (free x hx))
    have tx:=((t x (clear hx)).contDiffAt ((conf_open n).mem_nhds (clear hx))).of_le
      (show (k:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
    have ax:=((sa r x (clear hx)).contDiffAt ((conf_open n).mem_nhds (clear hx))).of_le
      (show (k:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
    rw [iteratedFDeriv_sub_apply tx ax]
    exact (norm_sub_le ..).trans (add_le_add left (by simpa only [A,WilsonThermometerWeakMeasuredSeries.approximate,pow_zero,mul_one] using right x hx))
  have smooth:∀ᶠ r in trail,ContDiffOn ℝ (p+1) (T r-A r) (conf n):=st.mono fun r t=>(t.sub (sa r)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact compact_signed positive (values R.family.S W Γ.date (fun r=>T r-A r) θ p p (by omega)
    decay positive Γ.upper smooth (flat _) nodes)

include run ms in
theorem Selected.grid_positions (Γ:Grid (ℓ:=ℓ) F H θ) (W:Finset E4) (j p q:ℕ)
    (retains:WilsonThermometerWeakSignedJets.high j p≤q) (temperature:Coupling G θ)
    (nodes:Nodes R.family.S W Γ.date (fun r=>measured F none (pub r) v r-approximate c q (θ r))
      θ (WilsonThermometerWeakSignedJets.high j p+1)) :
    ∀ K, IsCompact K → K⊆conf n → ∀ ε:ℝ,0<ε → ∀ᶠr in trail, ∀x∈K,∀viewer:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F viewer (pub r) v r) x-
        iteratedFDeriv ℝ j (approximate c p (θ r)) x‖≤ε*(θ r)^p :=
  run.mixed_positions Z M ms ν v within j p 0 q retains temperature
    (fun a _=>ms_regular Z M ms ν H (commonCaps v within) a)
    (run.grid_tests Z M ms ν v within Γ W _ q temperature nodes)

end YM.Integration.WilsonViewerElectedHierarchy
end
