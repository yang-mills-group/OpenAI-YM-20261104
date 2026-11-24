import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sleet
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local

/-!
# The unknown e: do not Taylor expand it

Distinguish an arbitrary subpopulation of the unmarked `R`'s affine-null regular family.
The listed Budget is IN ADDITION to the input requirement of E6 on the whole E family. Use
its sharp order to gain an extra fugacity on terms it touches. Projection uses full support
payments and the same inspections as the baseline Intake. Kernel still unmodified when these
expenses are counted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Inherit

open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior  Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Coat Raw
open Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint AnalyticBridge
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {n c f L : Side} {P : Teller G} {S : StepData c f} {T : Tube G S}
variable {k : Finset ℕ} {R : Rep G f} {δ A α β γ d η σ W s b μ : ℝ} {j B : ℕ}

section subpopulation

def selected (R : Rep G f) (E : Set ℕ) : Activities G f :=
    {R.activities with E := fun i=> if i ∈ E then R.activities.E i else 0}

def Debits (R : Rep G f) (E : Set ℕ) (C : ℝ) : Prop := (selected R E).EBound R.p C
lemma loosens (E : Set ℕ) (a b : ℝ) (h : Debits R E a) (hh : a≤b) : Debits R E b := by
  obtain ⟨u,hu,hU⟩:= h
  exact ⟨u,hu, fun i=> budget_loosen (hU i) hh⟩
lemma none_debited (a : ℝ) (ha : 0≤a) (R : Rep G f) : Debits R ∅ a := by
  refine ⟨fun _=>0,fun i=>?_,fun i=>?_⟩
  · unfold selected; simp only [Set.notMem_empty,↓reduceIte]
    simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=R.p) (X:=(R.activities.reg i).support) (o:=(R.activities.reg i).site) 0)
  simp only [SumBudget,BudgetPoint.mass,mul_zero,ite_self,summable_zero,true_and,tsum_zero]
  exact ⟨fun _=>le_rfl, by exact ha⟩

-- budget loosening & masks
lemma flagged (hp : Intake P T s R) (E : Set ℕ) : (selected R E).RegularFamily R.p := by
  have ht:= hp.cap.labels.regular
  refine ⟨fun i=>?_,fun i=>?_,fun i hi x y hx hy=>?_⟩
  all_goals unfold selected; dsimp only; split
  · exact ht.smooth _
  · exact CouplingShape.reg_const _
  · exact ht.at_flat _
  · rfl
  · exact ht.vanish _ hi _ _ hx hy
  · simp [logHessian]
end subpopulation

lemma fee_shift {ι : Type*} {X : ι→Support c} {B : ℕ} {a w : ℝ} {x : ι→ℕ} {u z : ι→ℝ}
    (hh : Sales B a α X (fun i=> u i * z i) x w) (hu : ∀ i, 1 ≤ u i) : Sales B a α X z x w := by
  have he i : 0 ≤ z i:= nonneg_of_mul_nonneg_right (hh.nonneg _) (zero_lt_one.trans_le (hu _))
  exact (one_mul w) ▸ hh.shift zero_le_one he fun i=> (le_mul_of_one_le_left (he i) (hu i)).trans_eq (by rw [one_mul])
lemma fee_plus {ι : Type*} {X : ι→Support c} {B : ℕ} {a b w : ℝ} {x : ι→ℕ} {u z : ι→ℝ}
    (hh : Sales B a α X u x w) (hu : Sales B a α X z x b) : Sales B a α X (u+z) x (w+b) := by
  refine ⟨fun i=> add_nonneg (hh.nonneg _) (hu.nonneg _), fun i=> ?_⟩
  convert budget_plus (hh.hit i) (hu.hit i) using 1; ext j
  by_cases hv:i ∈ X j <;> simp [hv,Reserves.tariff,add_mul]
lemma fee_cases {ι : Type*} {X : ι→Support c} {B : ℕ} {a b w : ℝ} {x : ι→ℕ} {u z : ι→ℝ}
    (hh : Sales B a α X u x w) (hu : Sales B a α X z x b) (p : ι→Prop) :
    Sales B a α X (fun i=> if p i then u i else z i) x (w+b) := by
  exact (one_mul (w+b)) ▸ (fee_plus hh hu).shift zero_le_one (fun i=> by
    split; exact hh.nonneg _; exact hu.nonneg _) (fun i=> by
    rw [one_mul,Pi.add_apply]; split; exact le_add_of_nonneg_right (hu.nonneg _); exact le_add_of_nonneg_left (hh.nonneg _))
lemma fee_times {ι : Type*} {X : ι→Support c} {B : ℕ} {a b w : ℝ} {x : ι→ℕ} {u : ι→ℝ}
    (hh : Sales B a α X u x w) (hb : 0≤b) : Sales B a α X (fun i=> b*u i) x (b*w) :=
  hh.shift hb (fun _=> mul_nonneg hb (hh.nonneg _)) (fun _=> le_rfl)

/-- Buyer for the distinguished subpopulation. -/
theorem project (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0 < ε)
    (ha : 0≤a) (hr : 4*ε < P.top.supportExponent) :
    ∃ n : ℕ, ∀ L : Side, n≤L.val → ∀ (u v : ℝ) (x : ℝ → ℝ), Rate G L u x → u<v →
    ∀ᶠ s : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (R : Rep G f),
      S.patch.L=L → Intake P T s R → ∀ E : Set ℕ, Debits R E (x s) →
      ∃ w, (∀ i ∈ E, ∀ U, |R.activities.regularOccurrence R.p i U| ≤ w i) ∧
        Sales (radiusB s) a ε (Raw.regularFoot S.ratio l (radiusB s) R) w (Raw.regularExtra R) (betaF G s L ^ v) := by
  have h := Fees.exponent (l+5) he ha (show 2*ε < P.top.supportExponent - 2*ε by linarith)
  obtain ⟨n,hn⟩ := h
  refine ⟨n,fun L hL u v X hX hv => ?_⟩
  let J (x : ℝ) := extentCost (l+5) (radiusB x)
  let bill (x d : ℝ) := Footprint.payment (L.val^4) (J x) 0 ε 1 d a (preCost (l+5))
  have hk : Rate G L u (fun x => bill x (X x)) := by
    have hh : Rate G L 0 (fun x : ℝ => (J x:ℝ)) := by simpa [extentCost,J] using
      (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
    simpa only [zero_add,bill] using! Rate.payment (Rate.const 1) hX hh (L.val^4) 0 ε a _
  filter_upwards [hk v hv, Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent by linarith)]
    with x hx hh c f S T R hP hR E hB
  let p:= S.ratio; let B:=radiusB x
  have hP' : p.count=L := hP
  obtain ⟨b,hw,h⟩ := hB
  let H := selected R E
  refine ⟨b,fun i hi U => ?_,?_⟩
  · unfold Activities.regularOccurrence; by_cases he' : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [masked_eq _ _ _ _ he']; have hU := (hw i).2 U he' [] (Nat.zero_le _) (by simp); unfold selected at hU; simpa only [leftDerivs,hi,↓reduceIte,Real.norm_eq_abs] using hU
    rw [masked_ne _ _ _ _ he',abs_zero]; exact (hw i).1
  let Y i := (R.activities.reg i).support
  have hY : Anchored (fun i => (R.activities.reg i).site) b (regularExtra R) (P.top.supportExponent)
      (X x) := by
    rw [hR.exponent]
    intro i; convert h i using 1; ext j; simp only [selected,BudgetPoint.mass,regularExtra]; rw [mul_comm]
  have hm := Sales.anchored_sale (z := b) (l:=l+5) (M := R.p.B) p (fun i => (R.activities.reg i).site) (Y := Y)
    (fun i => (R.activities.reg i).anchor) hY (fun i => (hw i).1)
    (X:=regularFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
    (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
    (fun i => ⟨(hw i).1,by simp⟩)
  apply hm.raise; rw [hP']; exact (le_abs_self _).trans hx

-- mask and control terms that are to be displayed at extra radii
abbrev sees (E : Set ℕ) (u : ℝ) (i : ℕ):ℝ:= if i∈E then u else 1

def weight (c f : Side) (E : Set ℕ) (u v : ℝ) : Raw.LogLetter c f → ℝ :=
    Sum.elim (sees E u) (Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (Sum.elim (fun _=>1)
      (Sum.elim (fun _=>v) (fun _=>v)))))
lemma weight_ge (E : Set ℕ) {u v : ℝ} (hu : 1≤u) (hv : 1≤v) (i : Raw.LogLetter c f) :
    1≤ weight c f E u v i := by
  rcases i with (i| (i| (i| (i| (i|i))))) <;> simp only [weight, sees, Sum.elim]; split; exact hu; exact le_rfl
  all_goals first| exact hv| rfl

end YM.RG01Estimate.Inherit
