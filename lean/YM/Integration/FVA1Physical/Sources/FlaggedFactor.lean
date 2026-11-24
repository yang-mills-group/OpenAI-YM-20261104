import YM.Integration.FVA1Physical.ExceptionalMass
import YM.Integration.FVA1Physical.Sources.CanonicalWindows
import YM.Integration.FVA1Physical.Sources.ModeCommute

/-! A cutoff-specific upper bound for the complementary joint reading using
the physical fields of the chosen batch and the actual coarse probability. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Function MeasureTheory Lattice RG RG.Supply Wilson Source Extra.Histories Org LocalLTE LocalLTE.Sail
open MergeProof MergeProof.Accent YM.Integration.FVA1Physical ConnectedActivityE6
open scoped BigOperators

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I]
variable {H : History G} {N n : ℕ} (B : Marker.Census I) (Y : Batch H N n I)

noncomputable def terminalFieldSize (j : I) : ℝ :=
  ‖(⟨Y.wavelengths j, physicalField_continuous Y j⟩ : C(Config G (H.S.side N n), ℂ))‖

/-- The marker exponential truncates at the number of original insertions.
Keep this finite-degree polynomial to avoid an exponential loss in the field sizes. -/
noncomputable def terminalInsertionBound : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card I + 1),
    ‖((k.factorial : ℂ)⁻¹)‖ * (∑ j, terminalFieldSize Y j) ^ k

/-- The original unnormalized birth polynomial divided by its genuine vacuum
has a test bound depending only on the displayed field sizes. -/
theorem physicalSeed_testBound (hH : H.Selected) (u : B.Mode → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (v : Config G (H.S.side N n)) :
    ‖((H.rep N n N).eval v)⁻¹ • modeTest u (Y.raw B v)‖ ≤
      terminalInsertionBound Y := by
  let q := (H.rep N n N).eval v
  let M := Mach B (fun j => Y.wavelengths j v)
  have hq : 0 < q := SectorNext.Vacuum.strictly H hH N n N le_rfl v
  change ‖q⁻¹ • modeTest u (q • Marker.Poly.pass M)‖ ≤ _
  rw [modeTest_real_smul, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hq.ne'), one_mul]
  have hM : Marker.Poly.price (fun _ => 1) M ≤ ∑ j, terminalFieldSize Y j := by
    apply (Marker.Poly.batch (fun _ => zero_lt_one) Finset.univ
      (fun j => Marker.Poly.send (B.fire j) (Y.wavelengths j v))).trans
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Marker.Poly.solo, Marker.Poly.solo_toll, one_mul]
    let F : C(Config G (H.S.side N n), ℂ) := ⟨Y.wavelengths j, physicalField_continuous Y j⟩
    change ‖F v‖ ≤ ‖F‖
    exact F.norm_coe_le_norm v
  apply (norm_modeTest_le_price u _ hu).trans
  apply (Marker.Poly.batch (fun _ => zero_lt_one) (Finset.range (Fintype.card I + 1))
    (fun k => ((k.factorial : ℂ)⁻¹) • M ^ k)).trans
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Marker.Poly.adapted]
  exact mul_le_mul_of_nonneg_left ((Marker.Poly.powers (fun _ => zero_lt_one) M k).trans
    (pow_le_pow_left₀ (Marker.Poly.nonnegative (fun _ => zero_lt_one) M) hM k)) (norm_nonneg _)

/-- This uses the actual coarse probability of *any* measurable event; the
constant is explicit for each original cutoff, volume and field batch. -/
theorem physicalEvent_testBound (hH : H.Selected) (u : B.Mode → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (i : ℕ) (hi : i ≤ N) (event : Set (Config G (H.S.side i n))) (he : MeasurableSet event) :
    ‖(∫ v in event, modeTest u (gust H N n N (Y.raw B) i hi v) ∂prior G (H.S.side i n)) /
      (Wilson.partition G (H.S.side N n) (H.β N n N) : ℂ)‖ ≤
      terminalInsertionBound Y * (OPE.Therm.scene H N n i).real event := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Wilson.partition_pos _).le]
  have heq := gust_modeTest_eq H N n (Y.raw B) (physicalSeed_integrable H hH B Y) u i hi
  rw [heq]
  exact gust_event_bound H hH N n (fun v => modeTest u (Y.raw B v)) _
    (physicalSeed_testBound B Y hH u hu) i hi event he

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A} {i : ℕ}

/-- The fine physical joint reading minus its localized coarse forecast is
bounded by the C18 power error plus the explicit exceptional-event charge. -/
theorem physicalTerminalError (Y : Batch (Issue.trail P) N n I)
    (π : ∀ j : ℕ, j ≤ N → Y.steering j)
    (fields : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
      Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
    (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i)) {p K : ℕ}
    (h : physicalTerminalStage B Y π fields hi O p K) (u : B.Mode → ℂ)
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    let H := Issue.trail P
    let Q := H.rep N n i
    let Q' := H.rep N n (i+1)
    let q := (A.B.a.clock.op i n).push Q'.beta Q'.eval
    let good := {v : Config G (H.S.side i n) | flags Q.p.threshold v = ∅}
    let predicted := fun v => Marker.Poly.pass (Sail.forecast B O (spectralValue Y π fields hi) v)
    let Z := Wilson.partition G (H.S.side N n) (H.β N n N)
    ‖((∫ v, modeTest u (Y.raw B v) ∂prior G (H.S.side N n)) -
      (∫ v in good, modeTest u (q v • predicted v) ∂prior G (H.S.side i n))) / (Z : ℂ)‖ ≤
      (Sail.margin K * 2) * Coat.gStep Q'.beta ^ ((p : ℝ) + 1) +
        terminalInsertionBound Y * (OPE.Therm.scene H N n i).real goodᶜ := by
  intro H Q Q' q good predicted Z
  let raw := gust H N n N (Y.raw B) i hi.le
  let f := ∫ v, modeTest u (Y.raw B v) ∂prior G (H.S.side N n)
  let exc := ∫ v in goodᶜ, modeTest u (raw v) ∂prior G (H.S.side i n)
  let model := ∫ v in good, modeTest u (q v • predicted v) ∂prior G (H.S.side i n)
  have he := physicalEvent_testBound B Y P.choice u hu i hi.le goodᶜ
    (flags_measurable_eq Q.p.threshold ∅).compl
  change ‖(f - model) / (Z : ℂ)‖ ≤ _
  rw [show (f - model) / (Z : ℂ) = (f - exc - model) / (Z : ℂ) + exc / (Z : ℂ) by ring]
  exact (norm_add_le _ _).trans (add_le_add (h u hu) he)

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
