import YM.Integration.WilsonTrueProjectedCourse

/-! A reported column may grow toward the upper cutoff. A loss strictly
below the true null exponent is summable directly in physical mesh time. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedTransportedFare
open Filter Lattice Wilson RG Source Labels
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonTrueProjectedColumnDescent WilsonTrueProjectedCourse
variable {G : Gauge}

def growth (C : Family G) (δ : ℝ) (m j : ℕ) := Real.exp (δ*(C.S.scale j-C.S.scale m))

theorem next (C : Family G) (δ : ℝ) (m j : ℕ) :
    decay C j * growth C δ m (j+1) = (factor C j)^(δ-GermGraph.rate)*growth C δ m j := by
  have hp : 0 < factor C j := zero_lt_one.trans (factor_positive C j)
  simp only [decay,growth,Schedule.scale_succ,Real.rpow_def_of_pos hp,←Real.exp_add]
  apply congrArg Real.exp
  change Real.log (C.S.block j).val * (-GermGraph.rate) +
      δ*(C.S.scale j+Real.log (C.S.block j).val-C.S.scale m) =
    Real.log (C.S.block j).val*(δ-GermGraph.rate)+δ*(C.S.scale j-C.S.scale m)
  ring

theorem accrue (C : Family G) {fee cap : ℕ → ℝ} (boundary : ℝ) (m b : ℕ)
    (positive : ∀ i ≥ m, i ≤ b → 0 ≤ cap i)
    (step : ∀ i ≥ m, i < b → decay C i * cap (i+1) + fee i ≤ cap i) :
    ∀ i ≥ m, ∀ n, i+n ≤ b →
      wallet C fee boundary n i ≤ retained C n i*boundary+cap i := by
  intro i mi n
  induction n generalizing i with
  | zero =>
    intro endpt
    simpa [wallet,retained] using positive i mi (by omega)
  | succ n ih =>
    intro endpt
    have h := ih (i+1) (by omega) (by omega)
    have pos : 0 ≤ decay C i := Real.rpow_nonneg (zero_le_one.trans (factor_positive C i).le) _
    calc
      wallet C fee boundary (n+1) i ≤ decay C i*(retained C n (i+1)*boundary+cap (i+1))+fee i :=
        add_le_add (mul_le_mul_of_nonneg_left h pos) le_rfl
      _ = retained C (n+1) i*boundary + (decay C i*cap (i+1)+fee i) := by rw [retained]; ring
      _ ≤ _ := add_le_add le_rfl (step i mi (by omega))

theorem scheduled (R : Run G) (simple : G.Simple) (q : ℕ) {δ M : ℝ} (gap : δ < GermGraph.rate)
    (mass : 0 ≤ M) {m b : ℕ} (mb : m ≤ b) (boundary : ℝ) (fee : ℕ → ℝ)
    (funded : ∀ i ≥ m, i < b → fee i ≤
      (1-(3:ℝ)^(δ-GermGraph.rate))*(M*power R q i*growth R.family δ m i)) :
    wallet R.family fee boundary (b-m) m ≤
      Real.exp (-GermGraph.rate*(R.family.S.scale b-R.family.S.scale m))*boundary + M*power R q m := by
  let C := R.family
  let cap := fun i => M*power R q i*growth C δ m i
  let ρ := (3:ℝ)^(δ-GermGraph.rate)
  have pn i : 0 ≤ power R q i := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have en i : 0 ≤ growth C δ m i := (Real.exp_pos _).le
  have cn i : 0 ≤ cap i := mul_nonneg (mul_nonneg mass (pn i)) (en i)
  have mono i : power R q (i+1) ≤ power R q i := by
    have dates := WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le_max_left 1 dates) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg q)) (by norm_num))
  have step (i : ℕ) (mi : m ≤ i) (ib : i < b) : decay C i*cap (i+1) + fee i ≤ cap i := by
    have width : (factor C i)^(δ-GermGraph.rate) ≤ ρ :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast C.S.block_large i) (sub_nonpos.mpr gap.le)
    have ratio : decay C i*cap (i+1) ≤ ρ*cap i := by
      calc
        _ = (decay C i*growth C δ m (i+1))*(M*power R q (i+1)) := by unfold cap; ring
        _ = ((factor C i)^(δ-GermGraph.rate)*growth C δ m i)*(M*power R q (i+1)) := by rw [next]
        _ ≤ (ρ*growth C δ m i)*(M*power R q i) :=
          mul_le_mul (mul_le_mul_of_nonneg_right width (en i))
            (mul_le_mul_of_nonneg_left (mono i) mass) (mul_nonneg mass (pn (i+1)))
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (en i))
        _ = ρ*cap i := by unfold cap; ring
    calc
      _ ≤ ρ*cap i+(1-ρ)*cap i := add_le_add ratio (funded i mi ib)
      _ = cap i := by ring
  have e := accrue C boundary m b (fun j _ _ => cn j) step m le_rfl (b-m) (by omega)
  rw [mesh_gain,show m+(b-m)=b by omega] at e
  simpa [cap,growth] using e

end YM.Integration.WilsonTrueProjectedTransportedFare
