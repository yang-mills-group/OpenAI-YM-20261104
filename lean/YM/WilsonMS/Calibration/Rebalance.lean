import YM.WilsonMS.Calibration.Rider
/-!
# Symmetrize all columns through the engineering horizon

Realization of simultaneously rotated world/pole data. This isn't regulator frame H
invariance at position center (indeed location convention choosing chamber needn't be!).
Will remove need for bounding a general non-equivariant matrix by passing exactly to
near-I leading branch even on regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Rider
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Landau Lattice Cylinder Native Lab Book Convolve Program
open Orient Tone Color Paint Wilsonian High Wind Wind.Leading Knobs Menus Land BMenu Trading Bin
  Outlook
open Logarithm
open scoped Topology ContDiff Interval Classical
variable {G : Gauge} {d : ℕ} (W : BasisMenu G) (T : MS_Data G (JRad.book G)) (p : Team)
local notation "B" => Ensure.deck G
section rotate
variable (V : Plaid (Ensure.deck G) d → Acts (Ensure.deck G) d) (t : Signed)
  (v : Plaid (Ensure.deck G) d)

def delivery (V : Plaid B d → Acts B d) (t : Signed) (v : Plaid (Ensure.deck G) d) : Acts B d :=
  (patrons Finset.univ (beta t⁻¹ v) (fun i => trade t (V i))).choose

lemma delivering : Ticket (delivery V t v) Finset.univ (beta t⁻¹ v) (fun i => trade t (V i)) :=
  (patrons _ _ _).choose_spec

lemma regional (a b : Glyph B d) (H : FitOrder a (V v 0)) (h : a.grade ≤ b.grade) :
    (trade t (V v) 0).register b = Polynomial.C (lines t a b) := by
  rw [ledger, Finset.sum_eq_single a, H.Single a le_rfl, if_pos rfl, Algebra.smul_def, mul_one]
  rfl
  · intro c hc hl
    by_cases he : a.grade ≤ c.grade
    rw [H.Single c he, if_neg hl, smul_zero]
    rw [show lines t c b = 0 from Classical.byContradiction fun hx => he ((bins t c b hx).2.symm ▸ h),
      zero_smul]
  simp

lemma truth_budget (h : ∀ i, FitOrder (Land.read i) (V i 0)) :
    FitOrder (Land.read v) (delivery V t v 0) := by
  have ht := delivering V t v
  constructor
  · intro x
    rw [ht.pf 0]
    simp_rw [Finset.sum_apply, sum_stack]
    refine Limit.sum _ fun i _ => ?_
    by_cases he : beta t⁻¹ v i = 0
    · rw [he, Complex.ofReal_zero, zero_smul]
      exact fun _ _ => rfl
    have hx : v.fst = i.fst := passes t⁻¹ v i he
    change
      Limit (((beta t⁻¹ v i : ℂ) • pose t ((V i 0).proof.input x) : Dot G Cover)).val
        ((v.fst.val : ℤ) - 1)
    rw [hx]
    exact Limit.smul _ (slimmer t (h i |>.Low x))
  intro b hb
  rw [ht.reg 0, Finset.sum_apply]
  have hp (i : Plaid B d) :
    ((beta t⁻¹ v i • (trade t (V i) 0).register) b) =
      Polynomial.C (beta t⁻¹ v i * lines t (Land.read i) b) := by
    rw [Pi.smul_apply]
    by_cases he : beta t⁻¹ v i = 0
    · rw [he, zero_smul, zero_mul, map_zero]
    rw [regional V t i _ b (h i) ?_, Algebra.smul_def, map_mul]
    rfl
    have hx := passes t⁻¹ v i he
    rw [show (Land.read i).grade = v.fst.val from congr_arg Fin.val hx.symm]
    exact hb
  have hs :
    ∑ i : Plaid B d, beta t⁻¹ v i * lines t (Land.read i) b = if b = Land.read v then 1 else 0 := by
    have hx := lines_mul (G := G) (d := d) t (Land.read v) b t⁻¹
    rw [mul_inv_cancel, lines_id] at hx
    rw [show (if (_ : Prop) then (1 : ℝ) else 0) = (if b = Land.read v then 1 else 0) from ?_] at hx
    swap
    · simp only [eq_comm (a := b)]
    rw [hx]
    conv_rhs => rw [Fintype.sum_sigma];
    symm
    rw [Finset.sum_eq_single (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1))]
    · rfl
    · intro a _ he
      apply Finset.sum_eq_zero
      intro i _
      rw [show lines t⁻¹ (Land.read v) ⟨a, i⟩ = 0 from ?_, zero_mul]
      exact Classical.byContradiction fun h => he (Fin.ext (bins t⁻¹ _ _ h |>.1.symm))
    simp
  simp_rw [hp, ← map_sum, hs]
  split <;> simp

lemma sailed (he : Fair W) (h : ∀ i, Fixed (col (rowFull W p (V i))) (Archive d (T.marks d i)) false d 0) :
    Fixed (col (rowFull W p (delivery V t v))) (Archive d (T.marks d v)) false d 0 := by
  let L (i : Plaid B d) := Archive d (T.marks d i)
  have hz (i : Plaid B d) :
    Fixed (col (rowFull W p (trade t (V i)))) (Trading.record t⁻¹ G (L i)) false d 0 := by
    rw [traded _ _ _ _ he]
    exact reserve t⁻¹ (h i)
  rw [row_mix _ _ (delivering V t v),
    show Archive d (T.marks d v) = ∑ i : Plaid B d, (beta t⁻¹ v i : ℂ) • Trading.record t⁻¹ G (L i)
      from ?_]
  exact trust_sum _ _ _ (fun i _ => trust_money (hz i) _)
  unfold L
  simp_rw [rota t T]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← beta_mul, mul_inv_cancel,
    beta_one]
  simp
variable {Z : Signed}

abbrev chargeH :=
  (Fintype.card Signed : ℝ)⁻¹

def balance (V : Plaid B d → Acts B d) (v : Plaid B d) : Acts B d :=
  (patrons Finset.univ (fun _ : Signed => chargeH) (fun t => delivery V t v)).choose

lemma balanced (V : Plaid B d → Acts B d) (v : Plaid B d) :
    Ticket (balance V v) Finset.univ (fun _ : Signed => chargeH) (fun t => delivery V t v) :=
  (patrons _ _ _).choose_spec

lemma mass {E : Type} [AddCommGroup E] [Module ℝ E] (v : E) : (∑ _i : Signed, chargeH • v) = v := by
  simp_rw [Finset.sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, chargeH,
    mul_inv_cancel₀ (by positivity : (Fintype.card Signed : ℝ) ≠ 0), one_smul]

lemma economy (h : ∀ i, FitOrder (Land.read i) (V i 0)) : FitOrder (Land.read v) (balance V v 0) := by
  have hp (i : Signed) := truth_budget V i v h
  constructor
  · intro x
    rw [(balanced V v).pf]
    simp_rw [Finset.sum_apply, sum_stack]
    exact Limit.sum _ (fun i _ => Limit.smul _ ((hp i).Low x))
  intro i hi
  rw [(balanced V v).reg, Finset.sum_apply]
  simp_rw [Pi.smul_apply,
    show ∀ t, (delivery V t v 0).register i = if i = Land.read v then 1 else 0 from fun t =>
      (hp t).Single i hi,
    mass]

lemma purse (hv : Fair W) (h : ∀ i, Fixed (col (rowFull W p (V i))) (Archive d (T.marks d i)) false d 0) :
    Fixed (col (rowFull W p (balance V v))) (Archive d (T.marks d v)) false d 0 := by
  rw [row_mix W p (balanced V v)]
  obtain hp :=
    trust_sum (h := (d : ℤ)) Finset.univ
      (fun t : Signed => (↑chargeH : ℂ) • col (rowFull W p (delivery V t v)))
      (fun _ => (↑chargeH : ℂ) • Archive d (T.marks d v))
      (fun t _ => trust_money (sailed W T p V t v hv h) _)
  have he : ∑ _i : Signed, (↑chargeH : ℂ) • Archive d (T.marks d v) = Archive d (T.marks d v) :=
    mass (Archive d _)
  rwa [he] at hp

def sameH (V : Plaid B d → Acts B d) : Prop :=
  ∀ (s : Signed) i k j,
    (trade s (V i) k).register j = ∑ v : Plaid B d, beta s i v • (V v k).register j

lemma trade_more (s : Signed) (X : Acts B d) (k : ℕ) (i : Glyph B d) :
    (trade s (trade t X) k).register i = (trade (s * t) X k).register i := by
  simp only [ledger, lines_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

lemma same (V : Plaid B d → Acts B d) : sameH (fun i => balance V i) := by
  have hs {I : Type} (a : Acts B d) (b : Finset I) (p : I → ℝ) (u : I → Acts B d)
    (hp : Ticket a b p u) (i : Glyph B d) (k : ℕ) (s : Signed) :
    (trade s a k).register i = ∑ j ∈ b, p j • ((trade s (u j) k).register i) := by
    rw [ledger, hp.reg]
    simp only [Finset.sum_apply, ledger, Finset.smul_sum, Pi.smul_apply, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  intro s i k j
  rw [hs _ _ _ _ (balanced V i)]
  simp only [show ∀ i : Plaid B d, _ from fun i => congr_fun ((balanced V i).reg k) j,
    Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm, ← Equiv.sum_comp (Equiv.mulLeft s)]
  refine Finset.sum_congr rfl fun q _ => ?_
  change
    chargeH • (trade s (delivery V q i) k).register j =
      ∑ l : Plaid B d, beta s i l • chargeH • (delivery V (s * q) l k).register j
  rw [hs _ _ _ _ (delivering V q i)]
  simp_rw [show ∀ l : Plaid B d, (delivery V (s * q) l k).register j = _ from fun l =>
      congr_fun ((delivering V (s * q) l).reg k) j,
    Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [trade_more]
  have ht : beta q⁻¹ i h = ∑ x : Plaid B d, beta s i x * beta (s * q)⁻¹ x h :=
    (by simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using beta_mul (s * q)⁻¹ s i h)
  rw [ht]
  simp_rw [Finset.sum_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [mul_smul, smul_comm chargeH]
end rotate
end YM.WilsonMS.Rider
