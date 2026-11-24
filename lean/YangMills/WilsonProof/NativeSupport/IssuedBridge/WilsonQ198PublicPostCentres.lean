import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslatedCompactRoom
import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198CommonCentres
import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Frame
import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Physical

set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace IssuedBridge.WilsonQ198PublicPostCentres
open YM YM.Integration Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FVA2 FVA2.Register FVA2.Scale Maxwell XSpace XSpace.Normalize
open WilsonNestedReportedCharacterCurrentBayQ198Physical
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {n : ℕ}

open YM.Integration.WilsonPositionHomogeneousFrame (homogeneous)
open YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Frame (archive name bounded)

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {κ : ℝ}
    (fund : FundedOriginalProperties.{u} hG κ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {b : ℕ} (hb : 0 < b) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower S)
    (Z : WilsonPrescription G) (lead : Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, Frame.obedient F A (J r) d)
    (d : Caps n) {K : Set (Points n)} (compact : IsCompact K) (safe : K ⊆ conf n)
    {θ : ℝ → ℝ} (heat : Trace.Pilot.Coupling G θ) {γ ε : ℝ} (hγ : γ < 4) (hε : 0 < ε) :
    ∀ᶠ r in RG17.home, ∀ x ∈ K, ∀ o : E4, ∀ t u : Viewers F,
      ∀ v : (i : Fin n) → Free R.family (d i),
        ‖Orbits.moment (spectator F t) (fun i => o + r • x.ofLp i) (fun i => homogeneous F J Z r (d i) (v i)) -
          Orbits.moment (spectator F u) (fun i => o + r • x.ofLp i) (fun i => homogeneous F J Z r (d i) (v i))‖ ≤
            ε * r ^ γ * ∏ i, ‖v i‖ := by
  obtain ⟨M, η, hM, hη, venue⟩ := _root_.PhysicalMatching.H7StandaloneTranslatedCompactRoom.original compact safe
  choose A₀ pos costs using fun i : Fin n => bounded F J Z hG lead paid (d i)
  let cap := ∏ i, A₀ i
  have cap0 : 0 ≤ cap := Finset.prod_nonneg fun i _ => pos i
  have large : 0 < cap + 1 := by linarith
  have budget := WilsonQ198CommonCentres.original hG W fund pace hb F fac Q J lead paid d hM hη heat
    (sub_pos.mpr hγ) (div_pos hε large)
  filter_upwards [budget, Filter.eventually_all.mpr costs, RG17.positiveLength] with r held limits rp x hx o t u v
  have room : WithinRoom r M η (fun i => o + r • x.ofLp i) o := by
    simpa only [_root_.PhysicalMatching.H7StandaloneTranslatedCompactRoom.translated, WithLp.ofLp_toLp] using venue r rp.le x hx o
  have distinct : Injective (fun i => o + r • x.ofLp i) := by
    intro i j eq
    by_contra ne
    have gap := room.spaced i j ne
    change o + r • x.ofLp i = o + r • x.ofLp j at eq
    rw [eq, sub_self, norm_zero] at gap
    exact (not_lt_of_ge gap) (by positivity)
  let a := fun i => archive F J Z r (d i) (v i)
  have before := held (fun i => o + r • x.ofLp i) o room distinct t u a
  have power : (4 : ℝ) - (4 - γ) = γ := by ring
  simp only [a, name, power] at before
  apply before.trans
  have dvd : (∏ i, ‖a i‖) ≤ cap * ∏ i, ‖v i‖ := by
    dsimp [cap]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => limits i (v i))
  have capFee : ε / (cap + 1) * cap ≤ ε :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)).trans_eq
      (div_mul_cancel₀ _ (ne_of_gt large))
  have nonneg : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have power0 : 0 ≤ r ^ γ := Real.rpow_nonneg rp.le _
  calc
    _ ≤ ε / (cap + 1) * r ^ γ * (cap * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_left dvd (by positivity)
    _ = (ε / (cap + 1) * cap) * (r ^ γ * ∏ i, ‖v i‖) := by ring
    _ ≤ ε * (r ^ γ * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_right capFee (by positivity)
    _ = _ := by ring

end IssuedBridge.WilsonQ198PublicPostCentres
