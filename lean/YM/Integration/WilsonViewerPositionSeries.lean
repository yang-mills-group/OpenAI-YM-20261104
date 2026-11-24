import YM.Integration.WilsonViewerPositionJets
import YM.Integration.WilsonThermometerWeakMeasuredSeries

/-! Uniformly charged separated tests of the original public frame determine its
position-space MS coefficients and every fixed physical derivative. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open WilsonPositionHomogeneousFrame WilsonThermometerWeakValueRecovery WilsonThermometerWeakCoefficientTail
open WilsonThermometerWeakMeasuredSeries WilsonPositionSeparatedProfileMatching
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν : ℝ) {n : ℕ}
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z

abbrev directions (R : Run G) (d : ℕ) (v : Fin n → Sec G d) : MaxwellSlots R.family (fun _ : Fin n => d) :=
  fun i => (Maxwell.Free.fields R.family.labels d).symm (v i)
abbrev coefficient (d : ℕ) (v : Fin n → Sec G d) (a : ℕ) : Points n → ℂ :=
  extended (fun x => WilsonPositionHomogeneousComparison.coefficient Z M ν d x v a)

include run in
/-- The input bound is uniform over the test ball at one fixed derivative order D. -/
theorem Selected.position (d : ℕ) (v : Fin n → Sec G d) (j p D q : ℕ)
    (retains : WilsonThermometerWeakSignedJets.high j p ≤ q) (temperature : Coupling G θ)
    (legal : ∀ a≤q, ContDiffOn ℝ ∞ (coefficient Z M ν d v a) (conf n))
    (signed : WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r => measured F none (pub r) (directions R d v) r -
        approximate (coefficient Z M ν d v) q (θ r)) θ (WilsonThermometerWeakSignedJets.high j p+1) D) :
    ∀ K, IsCompact K → K ⊆ conf n → ∀ ε : ℝ, 0<ε → ∀ᶠ r in trail, ∀ x∈K, ∀ viewer : Viewers F,
      ‖iteratedFDeriv ℝ j (measured F viewer (pub r) (directions R d v) r) x -
        iteratedFDeriv ℝ j (approximate (coefficient Z M ν d v) p (θ r)) x‖ ≤ ε*(θ r)^p := by
  let c := coefficient Z M ν d v
  let w := directions R d v
  let T := fun r => measured F none (pub r) w r
  let A := fun r => approximate c q (θ r)
  let B := fun r => approximate c p (θ r)
  have pq : p≤q := (Nat.le_succ p).trans ((Nat.le_mul_of_pos_left (p+1) (pow_pos (by decide) j)).trans retains)
  have polynomialSmooth (k : ℕ) (hk : k≤q) (r : ℝ) : ContDiffOn ℝ ∞ (approximate c k (θ r)) (conf n) :=
    smooth c _ _ fun a ha => legal a ((Nat.le_of_lt_succ (Finset.mem_range.mp ha)).trans hk)
  have st : ∀ᶠ r in trail, ContDiffOn ℝ ∞ (T r) (conf n) := RG17.positiveLength.mono
    fun r hr => WilsonThermometerWeakMeasuredBounds.unselected F pub w r hr
  have sa : ∀ᶠ r in trail, ContDiffOn ℝ ∞ (A r) (conf n) := Eventually.of_forall (polynomialSmooth q le_rfl)
  have sb : ∀ᶠ r in trail, ContDiffOn ℝ ∞ (B r) (conf n) := Eventually.of_forall (polynomialSmooth p pq)
  have decay := Coupling.conforms simple temperature
  have positive := temperature.positive
  have flat (k : ℕ) : Bounded trail (conf n) (fun r => T r-A r) k := by
    have finite := WilsonThermometerWeakCoefficientTail.original (conf_open n) c (Finset.range (q+1)) θ k 0
      (fun a ha => legal a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))) (fun a _ => Nat.zero_le a)
      decay (positive.mono fun _ h => h.le)
    intro K compact clear
    obtain ⟨U,Un,free⟩ := WilsonThermometerWeakMeasuredBounds.maxwell w K compact clear k
    obtain ⟨V,Vn,printed⟩ := finite K compact clear
    have close := WilsonPositionHomogeneousLeading.jets F J Z run.leading run.obeys simple
      (fun _ : Fin n => d) w k compact clear zero_lt_one
    refine ⟨1+U+V,by positivity,?_⟩
    filter_upwards [close,printed,st,sa] with r paid right t a x hx
    have left : ‖iteratedFDeriv ℝ k (T r) x‖ ≤ 1+U :=
      (norm_le_norm_sub_add _ (iteratedFDeriv ℝ k (WickGoal w) x)).trans (add_le_add (paid x hx) (free x hx))
    have tx := ((t x (clear hx)).contDiffAt ((conf_open n).mem_nhds (clear hx))).of_le
      (show (k : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have ax := ((a x (clear hx)).contDiffAt ((conf_open n).mem_nhds (clear hx))).of_le
      (show (k : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    rw [iteratedFDeriv_sub_apply tx ax]
    exact (norm_sub_le ..).trans (add_le_add left (by simpa only [A,WilsonThermometerWeakMeasuredSeries.approximate,pow_zero,mul_one] using right x hx))
  have measured' := WilsonThermometerWeakSignedJets.measured (conf_open n) Subset.rfl θ j p D decay positive
    (fun r => T r-A r) ((st.and sa).mono fun _ h => h.1.sub h.2) signed (flat _) (fun k _ _ => flat k)
  have cut : (fun r => A r-B r) = fun r => WilsonThermometerWeakCoefficientTail.part c (Finset.Ico (p+1) (q+1)) (θ r) := by
    funext r x
    change (∑ a∈Finset.range (q+1),(θ r)^a • c a x)-(∑ a∈Finset.range (p+1),(θ r)^a • c a x)=_
    rw [←Finset.sum_range_add_sum_Ico (fun a => (θ r)^a • c a x) (Nat.succ_le_succ pq)]
    dsimp [WilsonThermometerWeakCoefficientTail.part]
    abel
  have tail := WilsonThermometerWeakCoefficientTail.original (conf_open n) c (Finset.Ico (p+1) (q+1)) θ j (p+1)
    (fun a ha => legal a (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2))
    (fun _ ha => (Finset.mem_Ico.mp ha).1) decay (positive.mono fun _ h => h.le)
  rw [←cut] at tail
  intro K compact sep ε ep
  have first := WilsonThermometerWeakSignedJets.restore (conf_open n) θ j p decay positive T B A st sa sb measured'
    tail K compact sep (ε/2) (half_pos ep)
  have viewers := run.jets Z w j p K compact sep temperature (half_pos ep)
  filter_upwards [first,viewers] with r ok all x hx viewer
  exact (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv ℝ j (T r) x) _).trans
    ((add_le_add (all x hx viewer none) (ok x hx)).trans_eq (by ring))

end YM.Integration.WilsonViewerElectedHierarchy
end
