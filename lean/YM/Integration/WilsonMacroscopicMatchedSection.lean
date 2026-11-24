import YM.Integration.WilsonMacroscopicTestedOutput

/-! A single linear lift on the actual identity-shift layout, with a raw
label norm bound. Correcting an independently specified output label by
only its observable discrepancy preserves its existing null component. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicMatchedSection
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMacroscopicDetector
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}

/-- Works on the supplied layout, for example also when the scene plan and
ledger have already been fixed there. The lift and null-space projection
are fixed before defects, forecasts, and exterior tests. -/
theorem purchased (F : Spec.Final R.family f V) (L : Layout F) (J : ℝ → PhysMS.tower V)
    (shift : L.shift=(fun _ _=>LinearEquiv.refl ..)) (H : ℕ)
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) H) :
    ∃ (p : ℕ) (c : ℝ) (E : ℝ → (RG17.Free R.family H →L[ℂ] R.family.label H)), 0≤c ∧
    ∀ᶠ r in Trace.Pilot.trail,
      (∀ v, master L H r (E r v)=J r H v) ∧
      ‖E r‖≤c * R.family.path.levels.clock.hatBeta (L.level r)^p := by
  let B := Module.finBasis ℂ (RG17.Free R.family H)
  let I := Fin (Module.finrank ℂ (RG17.Free R.family H))
  let a (i : I) := (B.coord i).toContinuousLinearMap
  let c := ∑ i : I, ‖a i‖*‖B i‖
  obtain ⟨p,buy⟩ := funds.affordability
  let cert (r : ℝ) (i : I) (w : R.family.label H) :=
    ‖w‖≤R.family.path.levels.clock.hatBeta (L.level r)^p*‖B i‖ ∧
    master L H r w=J r H (B i)
  let row (r : ℝ) (i : I) := if h : ∃ w,cert r i w then h.choose else 0
  let E (r : ℝ) := ∑ i : I, (a i).smulRight (row r i)
  have cpos : 0≤c := Finset.sum_nonneg (fun i _=>mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
  refine ⟨p,c,E,cpos,?_⟩
  filter_upwards [buy] with r hr
  let b := R.family.path.levels.clock.hatBeta (L.level r)^p
  have sales (i : I) : cert r i (row r i) := by
    obtain ⟨w,cost,equal⟩ := hr.1 (B i)
    change mass R.family H (L.shift H r w)≤b*‖B i‖ at cost
    rw [shift] at cost
    have h : ∃ w,cert r i w := ⟨w,(RG12.norm_le_mass R.family H w).trans cost,equal⟩
    dsimp only [row]
    rw [dif_pos h]
    exact h.choose_spec
  have atv (v : RG17.Free R.family H) : E r v=∑ i : I, (B.repr v i) • row r i := by
    simp [E,a,Module.Basis.coord_apply]
  constructor
  · intro v
    rw [atv,map_sum]
    calc
      _ = ∑ i : I, B.repr v i • J r H (B i) := Finset.sum_congr rfl fun i _=>by rw [map_smul,(sales i).2]
      _ = J r H (∑ i : I, B.repr v i • B i) := by rw [map_sum]; simp only [map_smul]
      _ = J r H v := congrArg (J r H) (B.sum_repr v)
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg cpos
      (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _))
    intro v
    rw [atv]
    calc
      _ ≤ ∑ i : I, ‖B.repr v i • row r i‖ := norm_sum_le ..
      _ ≤ ∑ i : I, ‖a i‖*‖B i‖*(b*‖v‖) := Finset.sum_le_sum fun i _=>by
        rw [norm_smul]
        have h := mul_le_mul ((a i).le_opNorm v) (sales i).1 (norm_nonneg _) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
        exact h.trans_eq (by ring)
      _ = c*b*‖v‖ := by rw [← Finset.sum_mul]; ring

/-- Given a prior raw column, match its physical output, paying only the
J-normalized observable discrepancy.  Applies to a perturbative forecast
at any order without a raw-coordinate identification or a new reader. -/
theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
    {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d) :
    ∃ L : Layout F,L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
    ∀ H : ℕ,∃ (p : ℕ) (c : ℝ) (E : ℝ → (RG17.Free R.family H →L[ℂ] R.family.label H)),
    0≤c ∧ ∀ᶠ r in Trace.Pilot.trail,
      ∀ (q : R.family.label H) (x : V.Field H),
        let err := (J r H).symm (x-master L H r q)
        let out := q+E r err
        master L H r out=x ∧ ‖out-q‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p*‖err‖ := by
  obtain ⟨_,_,L,_,_,eqL,shift,buy,_⟩ :=
    WilsonReportPrescribedFrame.selected hG W source pace hB F fac J leading paid
  refine ⟨L,eqL,fun H=>?_⟩
  obtain ⟨p,c,E,hc,read⟩ := purchased F L J shift H (buy H)
  refine ⟨p,c,E,hc,?_⟩
  filter_upwards [read] with r h q x
  dsimp only
  constructor
  · rw [map_add,h.1,LinearEquiv.apply_symm_apply]; abel
  · rw [add_sub_cancel_left]
    exact ((E r).le_opNorm _).trans (mul_le_mul_of_nonneg_right h.2 (norm_nonneg _))

end YM.Integration.WilsonMacroscopicMatchedSection
