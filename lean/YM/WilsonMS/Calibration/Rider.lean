import YM.WilsonMS.Calibration.BinShift
/-!
# Table operations on registered labels

Retain track of the exact adjustments. `trade` changes the pose and includes value tuple
regroup at a fixed rate. No horizon truncation of $T$. Later need grade 0.
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
variable {G : Gauge} {d : ℕ} (W : BasisMenu G) (s : Signed) (p : Team)
local notation "B" => Ensure.deck G

variable (A : Acts (Ensure.deck G) d)

def trade (s : Signed) (A : Acts B d) : Acts B d := fun k =>
  let V := (A k).proof
  { register i := ∑ t : Glyph B d, lines s t i • (A k).register t
    proof :=
      { input x := pose s (V.input x)
        allowance := V.allowance
        actual x := bump s (V.actual x)
        calm x := keepsInk s (V.calm x)
        polyn := V.polyn.linear ((pose s).restrictScalars ℝ)
        ranks x := slimmer s (V.ranks x) } }

lemma ledger (k : ℕ) (i : Glyph B d) :
    (trade s A k).register i = ∑ t : Glyph B d, lines s t i • (A k).register t :=
  rfl

structure Fair (W : BMenu.BasisMenu G) : Prop where
  acts {j : ℕ} (s : Signed) p (i : Glyph B j) x k :
    pose s (W.pre p i x k) = ∑ j, (lines s i j : ℝ) • W.pre p j x k

lemma actsPre (W : XSpace.Initialize G) : Fair (↑W : BasisMenu G) := ⟨by
    intro j s p i x k; exact preamble_act s W p i x k⟩

lemma trade_w (hf : Fair W) (x : ℝ) (n : ℕ) : scoreW W p (trade s A) x n = pose s (scoreW W p A x n) := by
  let Y := trade s A
  unfold scoreW
  simp only [Pi.add_apply, map_add]
  congr 1
  · have ht (i : Glyph B d) (k : ℕ) :
      oil (trade s A) i k x = ∑ t : Glyph B d, (lines s t i : ℂ) * oil A t k x := by
      unfold oil
      rw [ledger]
      simp [Polynomial.eval_finsetSum]
    unfold rentW
    simp_rw [map_sum, map_smul, hf.acts, Finset.smul_sum, ht, Finset.sum_smul]
    let F (i j : Glyph B d) (u : ℕ × ℕ) := lines s j i • (oil A j u.1 x • W.pre p i x u.2)
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, smul_comm]
    rfl
  rw [sky, sky, map_add]
  exact
    congr_arg₂ _ (Eq.symm (Trading.lamp s _))
      (by
        rw [map_sum]
        exact
          Finset.sum_congr rfl fun k _ => (guide_stood s ((core_circle G p).stance0 x _ rfl) |>.symm))

lemma traded (hf : Fair W) : rowFull W p (trade s A) = Trading.moved G s⁻¹ (rowFull W p A) :=
  Trading.colourP s⁻¹ (skyPC G p) (feeds W p A) (feeds W p (trade s A)) fun i x => by
    rw [trade_w _ _ _ _ hf]
    simpa only [inv_inv] using pose_run s⁻¹ (scoreW W p A x i)

variable {I : Type}

structure Ticket (a : Acts B d) (P : Finset I) (c : I → ℝ) (V : I → Acts B d) : Prop where
  reg k : (a k).register = ∑ i ∈ P, c i • ((V i k).register)
  pf k : (a k).proof.input = ∑ i ∈ P, (c i : ℂ) • (V i k).proof.input

lemma patrons (P : Finset I) (c : I → ℝ) (V : I → Acts B d) : ∃ a : Acts B d, Ticket a P c V := by
  classical
  have he (k : ℕ) (P : Finset I) :
    ∃ a : Menus.Power G, a.input = ∑ i ∈ P, (c i : ℂ) • (V i k).proof.input := by
    induction P using Finset.induction with
    | empty =>
      exact
        ⟨0, by
          rw [Finset.sum_empty]
          rfl⟩
    | insert i s h ih =>
      obtain ⟨a, ha⟩ := ih
      let y := (V i k).proof
      let p' : Menus.Power G :=
        { input := (c i : ℂ) • y.input, allowance := y.allowance,
          actual := fun x => Tune.cash _ (by simp) (y.actual x), polyn := y.polyn.scale (c i),
          calm := fun x => (y.calm x).smul (c i : ℂ), ranks := fun x => (y.ranks x).smul (c i : ℂ) }
      refine ⟨p'.sub a.negate, ?_⟩
      rw [Finset.sum_insert h, ← ha]
      change (c i : ℂ) • y.input - (-a.input) = _
      rw [sub_neg_eq_add]
  choose t ht using fun k => he k P
  exact ⟨(fun k => ⟨∑ i ∈ P, c i • ((V i k).register), t k⟩), fun k => rfl, ht⟩
variable {P : Finset I} {u : I → ℝ} {V : I → Acts (Ensure.deck G) d} {a : Acts (Ensure.deck G) d}

lemma canvas (h : Ticket a P u V) : scoreW W p a = ∑ i ∈ P, (u i : ℂ) • scoreW W p (V i) := by
  have he (g : Glyph B d) k x : oil a g k x = ∑ i ∈ P, (u i : ℂ) * oil (V i) g k x := by
    unfold oil
    rw [h.reg, Finset.sum_apply]
    simp [Polynomial.eval_finsetSum]
  funext x k
  simp only [scoreW, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_add, sum_add_distrib]
  congr 1
  · unfold rentW
    simp_rw [he, Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm (f := fun i g => ∑ j ∈ Finset.antidiagonal k, (u i : ℂ) • _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_smul ..
  simp only [sky, h.pf, Finset.sum_apply, map_sum, Pi.smul_apply, map_smul, smul_add, sum_add_distrib,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma row_mix (h : Ticket a P u V) :
    col (rowFull W p a) = ∑ i ∈ P, (u i : ℂ) • col (rowFull W p (V i)) := by
  have he : rowFull W p a = ∑ i ∈ P, (u i : ℂ) • rowFull W p (V i) :=
    funext fun n =>
      mark_birth (feeds W p a) (PMsum _ _ _ fun i _ => PMscale (feeds W p (V i)) (u i))
        (fun i h' x => congr_fun (congr_fun (canvas W p h) x) i) n (Nat.lt_succ_self n)
  funext n t
  rw [he]
  change (∑ i ∈ P, (u i : ℂ) • rowFull W p (V i)) n t.1 (exp t.2) = _
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl
end YM.WilsonMS.Rider
