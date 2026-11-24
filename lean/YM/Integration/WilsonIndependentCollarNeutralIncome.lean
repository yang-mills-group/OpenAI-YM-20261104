import YM.Integration.WilsonThermometerUnitFilingWeakChain
import YM.Integration.WilsonThermometerUnitFilingWeakPair

/-! At a moving report, charge the absolute kernel of each unchanged Gaussian
leg at the genuine child. A fixed number of Ward, Wick or joining vertices
can separate arbitrarily long such intervals on the same original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarNeutralIncome
open Filter Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08 Wilson FormalBulk08 Flat
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingWeakChain WilsonThermometerUnitFilingWeakRibbon
open scoped Classical BigOperators
variable {G : Gauge}

def absoluteRow {I J : Type} (A : Bloch.Row I J) : Bloch.Row I J :=
  fun i j d => ‖A i j d‖

private theorem after_absolute {I J : Type} [Fintype J] (L : Side) (s : ℝ) (A : Bloch.Row I J)
    {r : ℕ} (x : Cover) (p : Fin r → Cover) (u : Fin r → I) (box : Fin r → Finset Cover) :
    after L s (absoluteRow A) x p u box = after L s A x p u box := by
  simp only [after,shifted,absoluteRow,norm_norm]

def kernelMass (R : Run G) (N : ℕ) (c : Bool) {r : ℕ} (derivative : ℕ → List Axis) (i : ℕ)
    (f : SiteList (face c) r → ℝ) (a : SiteList (face c) r) : ℝ :=
  let P := current R N i
  ∑' z, term P.L (absoluteRow (kernel c R.metals.p.kernel P (derivative i)))
    (fun j => (wrap P.L (a.sites j),a.face j)) a f z

abbrev width (Q : WilsonOriginalCompoundStrip.Request G) (R : Run G) (h i : ℕ) :=
  WilsonThermometerUnitFilingWeakStrip.trial Q R.metals.p.kernel (R.alloy.B.a.clock.J i) h

/-- The sum of the absolute path salaries is bounded before any cancellations.
The date, number of steps, held roots and angular slots remain free. -/
theorem original (Q : WilsonOriginalCompoundStrip.Request G) (R : Run G)
    (fund : WilsonOriginalProfileStrip.Filed (WilsonOriginalCompoundStrip.programme
      (WilsonThermometerUnitFilingWeakStrip.enrolled Q)) R.kit)
    (v N H : ℕ) (room : H ≤ R.alloy.B.a.clock.J v) (start : 4 ≤ R.alloy.B.a.clock.J v)
    (c : Bool) (l : ℕ → List Axis) (orders : ∀ i, v ≤ i → i < N →
      (l i).length ≤ R.alloy.B.a.clock.J (i+1)-2)
    (r : ℕ) (f : SiteList (face c) r → ℝ) (paid : ∀ a, ‖f a‖ ≤ rentAt (width Q R H v) a)
    (n : ℕ) (live : v+n ≤ N) (a : SiteList (face c) r) :
    ‖walk (kernelMass R N c l) v f n a‖ ≤ rentAt (width Q R H (v+n)) a := by
  induction n generalizing a with
  | zero => exact paid a
  | succ n ih =>
    let i := v+n
    let P := current R N i
    have low : v ≤ i := Nat.le_add_right _ _
    have before : i<N := by dsimp [i]; omega
    have m₀ := R.alloy.B.a.fits.mono low
    have m₁ := R.alloy.B.a.fits.mono (Nat.le_succ i)
    have rows := WilsonThermometerUnitFilingWeakStep.bought Q R fund i H (room.trans m₀)
      (start.trans (m₀.trans m₁)) (start.trans m₀) (R.alloy.B.a.fits.stepSlow i) (Nat.le_succ _)
      P (WilsonThermometerUnitFilingWeakStep.block R N i) (l i) (orders i low before) r a.origin a.sites
    have h : ∀ box : Fin r → Finset Cover,
        after P.L (width Q R H i) (absoluteRow (kernel c R.metals.p.kernel P (l i))) a.origin a.sites
          (fun j => (wrap P.L (a.sites j),a.face j)) box ≤ rentAt (width Q R H (i+1)) a := by
      intro box
      rw [after_absolute]
      cases c with
      | true => exact rows.1 _ _
      | false => exact rows.2 _ _
    exact (row P.L _ _ a h _ (ih (by omega))).2

/-- A rooted finite stencil or sum of compatible source atoms puts its
entire external engineering and Laurent price outside the neutral walk. -/
theorem source {ι : Type*} (Q : WilsonOriginalCompoundStrip.Request G) (R : Run G)
    (fund : WilsonOriginalProfileStrip.Filed (WilsonOriginalCompoundStrip.programme
      (WilsonThermometerUnitFilingWeakStrip.enrolled Q)) R.kit)
    (v N H : ℕ) (room : H ≤ R.alloy.B.a.clock.J v) (start : 4 ≤ R.alloy.B.a.clock.J v)
    (c : Bool) (l : ℕ → List Axis) (orders : ∀ i, v ≤ i → i<N →
      (l i).length ≤ R.alloy.B.a.clock.J (i+1)-2)
    (r : ℕ) (f : SiteList (face c) r → ℝ) (paid : ∀ a, ‖f a‖ ≤ rentAt (width Q R H v) a)
    (n : ℕ) (live : v+n ≤ N) (S : Finset ι) (dose : ι → ℂ) (root : ι → SiteList (face c) r)
    {H₀ : ℝ} (issued : ∑ t ∈ S, ‖dose t‖ * rentAt (width Q R H (v+n)) (root t) ≤ H₀) :
    ∑ t ∈ S, ‖dose t‖ * ‖walk (kernelMass R N c l) v f n (root t)‖ ≤ H₀ := by
  apply le_trans (sum_le_sum fun t _ => ?_) issued
  exact mul_le_mul_of_nonneg_left
    (original Q R fund v N H room start c l orders r f paid n live _) (norm_nonneg _)

end YM.Integration.WilsonIndependentCollarNeutralIncome
