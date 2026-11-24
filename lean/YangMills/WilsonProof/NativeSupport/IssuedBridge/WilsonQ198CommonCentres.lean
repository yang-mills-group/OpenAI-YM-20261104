import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Physical

set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace IssuedBridge.WilsonQ198CommonCentres
open YM YM.Integration Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonNestedReportedCharacterCurrentBayQ198Physical
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {n : ℕ}

private theorem frame (d : Caps n) : ∃ c : ℝ, 0≤c ∧
    ∀ m : MultilinearMap ℂ (fun i=>Free R.family (d i)) ℂ,∀ b : ℝ,
    (∀ a : Code (fun i=>Free R.family (d i)),‖m (combination _ a)‖≤b) → ∀ v,‖m v‖≤c*b*(∏ i,‖v i‖) := by
  let P (i : Fin n) := Free R.family (d i)
  let coordinates (a : Code P) (i : Fin n) := ((Module.finBasis ℂ (P i)).coord (a i)).toContinuousLinearMap
  let size (a : Code P) := ∏ i,‖coordinates a i‖
  have sn (a : Code P) : 0 ≤ size a := prod_nonneg fun _ _=>ContinuousLinearMap.opNorm_nonneg _
  have invoice (a : Code P) (v : (i:Fin n)→P i) : ‖coords P a v‖ ≤ size a*∏ i,‖v i‖ := by
    unfold coords size;rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(coordinates a i).le_opNorm _)
  refine ⟨∑ a : Code P,size a,sum_nonneg (fun a _=>sn a),?_⟩
  intro m b row v
  let v₀ := ∏ i,‖v i‖
  have vn : 0≤v₀ := prod_nonneg fun i _=>norm_nonneg _
  rw [basis_tuple P v m]
  calc
    _ ≤ ∑ a : Code P, ‖coords P a v*m (combination P a)‖ := norm_sum_le ..
    _ ≤ ∑ a : Code P,size a*(b*v₀) := sum_le_sum fun a _=>by
      rw [norm_mul];exact (mul_le_mul (invoice a v) (row a) (norm_nonneg _) (mul_nonneg (sn a) vn)).trans_eq (by ring)
    _ = (∑ a : Code P,size a)*(b*v₀) := (sum_mul ..).symm
    _ = _ := (mul_assoc ..).symm


theorem fixed {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {κ : ℝ}
    (fund : FundedOriginalProperties.{u} hG κ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {b : ℕ} (hb : 0 < b) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower S)
    (lead : Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, Frame.obedient F A (J r) d)
    (d : Caps n) (v : (i : Fin n) → Free R.family (d i)) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    {θ : ℝ → ℝ} (heat : Trace.Pilot.Coupling G θ) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∀ᶠ r in RG17.home, ∀ (x : Fin n → E4) (o : E4), WithinRoom r M η x o → Injective x →
      ∀ t u : Viewers F,
      ‖Orbits.moment (spectator F t) x (fun i => J r (d i) (v i)) -
        Orbits.moment (spectator F u) x (fun i => J r (d i) (v i))‖ ≤ ε * r ^ ((4 : ℝ) - σ) := by
  have both := WilsonMacroscopicPrescribedInputs.original hG W fund pace hb F fac Q J lead paid d v
    (voices (ghosts S)) hM hη (by norm_num : (0 : ℝ) < 1) heat 3 0 hσ (half_pos hε)
  filter_upwards [both] with r hr x o fits distinct t u
  let labels := fun i => J r (d i) (v i)
  let c := coefficient F Q x labels o
  have bound (s : Viewers F) :
      ‖Orbits.moment (spectator F s) x labels - c‖ ≤ (ε/2) * r ^ ((4 : ℝ) - σ) := by
    rw [show Orbits.moment (spectator F s) x labels - c =
        formula F Q x o labels OPE.Short.gapPos (voices (ghosts S)) 3 s from
      identity F Q hG x labels o s distinct]
    have hh := hr x o OPE.Short.gapPos fits (by constructor <;> intro z <;> cases z) s
    norm_num at hh
    exact hh
  calc
    _ = ‖(Orbits.moment (spectator F t) x labels - c) -
        (Orbits.moment (spectator F u) x labels - c)‖ := by congr 1; abel
    _ ≤ _ := norm_sub_le _ _
    _ ≤ (ε/2) * r ^ ((4 : ℝ) - σ) + (ε/2) * r ^ ((4 : ℝ) - σ) := add_le_add (bound t) (bound u)
    _ = _ := by ring

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {κ : ℝ}
    (fund : FundedOriginalProperties.{u} hG κ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {b : ℕ} (hb : 0 < b) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower S)
    (lead : Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, Frame.obedient F A (J r) d)
    (d : Caps n) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) {θ : ℝ → ℝ}
    (heat : Trace.Pilot.Coupling G θ) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∀ᶠ r in RG17.home, ∀ (x : Fin n → E4) (o : E4), WithinRoom r M η x o → Injective x →
      ∀ t u : Viewers F, ∀ v : (i : Fin n) → Free R.family (d i),
      ‖Orbits.moment (spectator F t) x (fun i => J r (d i) (v i)) -
        Orbits.moment (spectator F u) x (fun i => J r (d i) (v i))‖ ≤
        ε * r ^ ((4 : ℝ) - σ) * ∏ i, ‖v i‖ := by
  let P (i : Fin n) := Free R.family (d i)
  obtain ⟨c, cn, contract⟩ := frame (R := R) d
  have cp : 0 < c+1 := by linarith only [cn]
  have all := eventually_all.mpr fun a : Code P =>
    fixed hG W fund pace hb F fac Q J lead paid d (combination P a) hM hη heat hσ (div_pos hε cp)
  filter_upwards [all, RG17.positiveLength] with r hr rp x o fits distinct t u v
  let m := (Orbits.moment (spectator F t) x - Orbits.moment (spectator F u) x).compLinearMap
    (fun i => (J r (d i)).toLinearMap)
  let z := r ^ ((4 : ℝ) - σ)
  have row (a : Code P) : ‖m (combination P a)‖ ≤ (ε / (c+1)) * z :=
    hr a x o fits distinct t u
  have cpay : c*(ε/(c+1)) ≤ ε := by rw [←mul_div_assoc, div_le_iff₀ cp]; nlinarith only [hε]
  calc
    _ = ‖m v‖ := rfl
    _ ≤ c * (ε / (c+1) * z) * (∏ i, ‖v i‖) := contract m _ row v
    _ = c * (ε / (c+1)) * z * (∏ i, ‖v i‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cpay (Real.rpow_nonneg rp.le _))
      (Finset.prod_nonneg fun i _ => norm_nonneg _)

end IssuedBridge.WilsonQ198CommonCentres
