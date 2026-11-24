import YM.Integration.WilsonIndependentCapturePeriod

/-! Cover and winding wages for a one-root field, starting at the scale of
its capture. All angular charges are homogeneous in that initial salary. -/
noncomputable section
namespace YM.Integration.WilsonIndependentFreshFiniteWage
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped ENNReal Classical
variable {W : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y)
  (T : S.Accounts) {m : ℕ} (Z : T.Report m) {p u b q e r : ℕ} {γ c₀ : ℝ}
  {c c' : Flap M → ℝ≥0∞} {x : W → Room} {L : Meter W}

def credit (γ : ℝ) (gross : W → ℝ≥0∞) (w : Page M) :=
  gross w.bindW * ENNReal.ofReal ((S.l (Page.opening M w.bindW) / S.l w)^γ)

def purse (γ : ℝ) (gross : W → ℝ≥0∞) (w : W) :=
  gross w * ENNReal.ofReal (S.l (Page.opening M w)^γ)

theorem value (γ : ℝ) (gross : W → ℝ≥0∞) (i : Page M) :
    ticket (S.softnessWeight γ) (purse S γ gross) i = credit S γ gross i := by
  change (_ * ENNReal.ofReal _) * (ENNReal.ofReal (S.l i^γ))⁻¹ =
    _ * ENNReal.ofReal ((S.l (Page.opening M i.bindW) / S.l i)^γ)
  rw [mul_assoc, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (S.hl _) _),
    Real.div_rpow (S.hl _).le (S.hl _).le]

/-- The authentic cover current at every age, including its arbitrary
positive-rank lower components, at the finite capture's relative tariff. -/
theorem cover (B : S.Primitive L p b) (N : S.Supplies T L p b)
    (soft : S.Softness u L c (S.softnessWeight γ) 1) (hu : u ≤ b)
    (gross : W → ℝ≥0∞) (finite : ∀ w, gross w ≠ ⊤)
    (wage : ∀ i, i ≤ p → ∀ r, 0 < r →
      Claim L (fun w => S.coverQ x u (Page.opening M w)) gross
        (fun w => Z.main (Page.opening M w) i r))
    (ward : ∀ j i, i ≤ p → (S.sight j).Way (Z.main j.prev) i)
    (he : e ≤ p) (hr : 0 < r) :
    Claim (coverL M L) (S.coverQ x u) (credit S γ gross) (fun j => Z.main j e r) := by
  let s := purse S γ gross
  have rows : S.Imprints T Z.main u p m x (S.softnessWeight γ) s 1 L := by
    refine ⟨?_, ?_, ward, fun w i _ => Z.cap_b B.grade w i,
      fun _ _ _ _ _ hlt => False.elim (by omega),
      fun w => ENNReal.mul_ne_top (finite w) ENNReal.ofReal_ne_top⟩
    · intro i hi r hr
      convert wage i hi r hr using 1
      funext w
      rw [show ticket (S.softnessWeight γ) s (Page.opening M w) = _ from value S γ gross _]
      change gross w * ENNReal.ofReal ((S.l (Page.opening M w) / S.l (Page.opening M w))^γ) = _
      rw [div_self (S.hl _).ne', Real.one_rpow, ENNReal.ofReal_one, mul_one]
    · intro i _ r
      have hh (j : Flap M) : Z.main j.next i r - S.reportOut T Z.main m j i r = 0 := by
        unfold reportOut
        rw [← Z.step_m j]
        exact sub_self _
      simp_rw [hh]
      exact Claim.zeroQ
  have h := S.glides T Z.main B N soft rows hu e he r hr
  have eq : ticket (S.softnessWeight γ) s = credit S γ gross := funext (value S γ gross)
  rwa [eq] at h

/-- A genuine unmarked discrepancy may already be present on the birth
page. Its original winding wage enters through the resident course. -/
theorem winding [∀ w, Fintype (Y w)]
    (H : WilsonIndependentResidentWinding.Resident S T 1 q p L)
    (lead : S.Lead 1 c') (soft : S.Softness 2 L c (S.softnessWeight γ) 1)
    (dc : S.cushion c₀ x) (hc : 0 < c₀) (hg : 0 ≤ γ) (hγ : γ ≤ 1)
    (big : ∀ j : Flap M, 1 ≤ S.l j.next)
    (scale : Poly (flapL M L) (fun j => ENNReal.ofReal (S.shift j)))
    (gross : W → ℝ≥0∞) (finite : ∀ w, gross w ≠ ⊤)
    (wage : ∀ i, i ≤ p → ∀ r, 0 < r → Claim L
      (fun w => S.coverQ x 2 (Page.opening M w)) gross (fun w => Z.main (Page.opening M w) i r))
    (ward : ∀ j i, i ≤ p → (S.sight j).Way (Z.main j.prev) i)
    (finiteWard : ∀ j i, i ≤ p → (S.sight j).WayO (Z.deviation j.prev) i)
    (he : e ≤ p) : Claim (coverL M L) (S.markUp x 0)
      (fun j => gross j.bindW * ENNReal.ofReal ((S.l (Page.opening M j.bindW) / S.P j.bindW)^γ))
      (fun j => Z.deviation j e r) := by
  apply WilsonIndependentResidentWinding.archive S T Z (u := 0) (b := 1) (x := x)
    (s := fun w => gross w * ENNReal.ofReal ((S.l (Page.opening M w) / S.P w)^γ)) H lead (t := fun j => credit S γ gross j.prev) _ _ he r
  refine {data := ?_, coin := fun j => ENNReal.mul_ne_top (finite _) ENNReal.ofReal_ne_top,
          ticket := ?_, ward := finiteWard}
  · intro i hi r hr
    exact S.prior _ (cover S T Z H.prim H.space soft (by omega) gross finite wage ward hi hr)
  · exact WilsonIndependentCapturePeriod.paid S L dc hc hg hγ big scale
      (fun w => S.l (Page.opening M w)) (fun _ => S.hl _) gross

end YM.Integration.WilsonIndependentFreshFiniteWage
