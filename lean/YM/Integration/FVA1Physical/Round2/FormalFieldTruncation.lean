import YM.Integration.FVA1Physical.Wilson.ExactOrder
import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.MSbar.CrossH.Mug

/-! Truncation of the same normalized Wilson polynomial in the full rooted
derivative budget, before any evaluation or choice of differentiations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice MSbar MSbar.Whisk MSbar.Cacao MSbar.CrossH MSbar.Rolling
open MSbar.Lis MSbar.Mosaic MSbar.Heath MSbar.Heath.Stock MSbar.Duel Push.Uniform
open MSbar.Bakery MSbar.Bakery.Film MSbar.Kelvin MSbar.Bulk MSbar.Bout Tree
open YM.Integration.FVA1Physical.Wilson RG YM.Wilson Precision Exterior
open scoped Classical Topology BigOperators
variable {σ : Type} [Fintype σ] {G : Gauge}

def renderedPolynomial {ι : Type} (U : PowerSeries (Pot ι)) (p : ℕ) (g : ℝ) : Pot ι :=
  ∑ i ∈ range (p+1),g^i • PowerSeries.coeff i U

theorem emitted_prefix (A : Issue G) (χ : ChartRatio G) (src : PowerSeries (Pot (Joint A.F G)))
    (kind : Kind A.T) (pd : (mold A.pre A.F A.v).PosDef) {p n : ℕ} (hp : p≤n) :
    Lap p (emittedRows A χ src n) (emittedRows A χ src p) := by
  have same : Lap p (normalizedRows A χ src n) (normalizedRows A χ src p) :=
    grow_prefix (straight A.F G) pd.inv (well A.F A.v χ _ kind) (well A.F A.v χ _ kind)
      (fun _ _=>rfl) (fun _ _=>rfl) (by omega) (by omega)
  intro i hi
  simp only [emittedRows,PowerSeries.coeff_map,same i hi]

theorem represented_truncation {c : Side} (loc : σ → Site c) (W : Finset (Site c))
    (ξ : View σ) (s k p d : ℕ) (A B : PowerSeries (Pot σ)) {g α H : ℝ}
    (hg : 0≤g) (h1 : g≤1) (same : Lap p A B)
    (caps : ∀ i : ℕ, p < i → i ≤ p+d → Vault loc W α s k ξ (PowerSeries.coeff i A) H) :
    Vault loc W α s k ξ (renderedPolynomial A (p+d) g-renderedPolynomial B p g)
      ((d:ℝ)*g^(p+1)*H) := by
  let f := fun i : ℕ=>g^i • PowerSeries.coeff i A
  have agree : (∑ i∈range (p+1),f i) = renderedPolynomial B p g := by
    apply sum_congr rfl
    intro i hi
    exact congrArg (g^i • ·) (same i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
  have split : renderedPolynomial A (p+d) g-renderedPolynomial B p g =
      ∑ j∈range d,f (p+1+j) := by
    rw [renderedPolynomial,show p+d+1=p+1+d by omega,sum_range_add]
    change (∑ i∈range (p+1),f i)+(∑ j∈range d,f (p+1+j))-_ = _
    rw [agree,add_sub_cancel_left]
  rw [split]
  have bank := Quote.total (fun j=>f (p+1+j)) (range d) (fun _=>g^(p+1)*H) (by
    intro j hj
    have inRange:=mem_range.mp hj
    have row:=caps (p+1+j) (by omega) (by omega)
    apply Quote.widen (Quote.mulR row (g^(p+1+j))) _ le_rfl
    rw [abs_of_nonneg (pow_nonneg hg _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hg h1 (by omega)) row.1)
  simpa [mul_assoc] using bank

theorem represented_trunk {c : Side} (loc : σ → Site c) (W : Finset (Site c))
    (ξ : View σ) (s k p : ℕ) (A : PowerSeries (Pot σ)) {g α H : ℝ}
    (hg : 0≤g) (h1 : g≤1)
    (caps : ∀ i ≤ p, Vault loc W α s k ξ (PowerSeries.coeff i A) H) :
    Vault loc W α s k ξ (renderedPolynomial A p g) (((p+1:ℕ):ℝ)*H) := by
  have bank:=Quote.total (fun i=>g^i • PowerSeries.coeff i A) (range (p+1)) (fun _=>H) (by
    intro i hi
    have row:=caps i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    apply Quote.widen (Quote.mulR row (g^i)) _ le_rfl
    rw [abs_of_nonneg (pow_nonneg hg _)]
    exact mul_le_of_le_one_left row.1 (pow_le_one₀ hg h1))
  simpa [renderedPolynomial] using bank

theorem rendered_emitted (A : Issue G) (χ : ChartRatio G) (src : PowerSeries (Pot (Joint A.F G)))
    (p : ℕ) (branch : A.S.patch.Branches A.S.kernel G)
    (prem : Premier (main A.f A.pre.clip A.pre.path)) (crit : Critical A.F A.pre.clip A.pre.path A.ρ)
    (pd : (mold A.pre A.F A.v).PosDef) (hg : A.fClock ≠ 0) (Z : Positions (Primary A.c G)) :
    clue (renderedPolynomial (emittedRows A χ src p) p A.fClock) Z =
      taste p (bulkColumn A χ (A.fClock • Z) src p) A.fClock := by
  unfold clue renderedPolynomial taste
  rw [map_sum]
  apply sum_congr rfl
  intro i _
  change MvPolynomial.eval Z (_ • _) = _ * PowerSeries.coeff i _
  rw [emitted_read A χ src p i branch prem crit pd (A.fClock • Z),inv_smul_smul₀ hg]
  simp [MvPolynomial.smul_eq_C_mul]

end YM.Integration.FVA1Physical.Round2.Curvature
