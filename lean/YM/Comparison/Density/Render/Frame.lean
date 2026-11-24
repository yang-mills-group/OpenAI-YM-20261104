import YM.Comparison.Density.Render.Belle

/-!
Orientation/compression toolkit; canon at every seat, complete masked
atoms. `tax` is orientation cardinality IN ADDITION to kernel mass on
this coefficient family. Marker-specific data use a different book.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision Work.F03 Work.G07 StressFlux
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {k t m : ℕ}

abbrev Cycle (n : Side) := Seat n × ℕ
structure Frame (G : Gauge) (n : Side) where
    footprint : ℕ → Support n
    pivot i : (0:Site n)∈ footprint i
    dataF : ℕ → Pot G n
namespace Frame
variable (F : Frame G n) (B : BudgetPoint) (A : Activities G n)
def shelf (j : Cycle n) := j.1.reg (F.footprint j.2) (F.pivot _)
-- put in factor in a already?
def table (j : Cycle n) := F.dataF j.2 ∘ j.1.view
def coffee : Activities G n:= ⟨F.shelf ∘ numbering _, A.forced,F.table ∘ numbering _, A.K⟩
structure Fair (F : Frame G n) (B : BudgetPoint) (c : ℕ →ℝ) : Prop where
    regular i : B.Regular (F.footprint i) (F.dataF i)
    charge i : B.supBounds 0 (F.footprint i) (F.dataF i) (c i)
structure Nulls (F : Frame G n) : Prop where
    one i : F.dataF i 1=0
    gone i : Nonwrapping (F.footprint i) 0 → ∀ x y,IsAffineDirection 0 x → IsAffineDirection 0 y → logHessian (F.dataF i) x y=0
-- zero padding
protected def move {p x} (ht : A.Moves p x): (F.coffee A).Moves p x:= by
  let Y:= numbering (Cycle n); let L:= Equiv.prodCongr (Seat.move p x) (Equiv.refl ℕ); let u:= (Y.trans L).trans Y.symm
  have he i : Y (u i)=L (Y i):= Y.apply_symm_apply _
  refine ⟨u,ht.kp,fun i=> ?_,fun i=>?_,ht.forced_support,ht.forced_inventory,ht.forced_tests,fun i U=>?_,ht.valuesK⟩
  · change (F.shelf (Y (u i))).site=_; rw [he]; rfl
  · change (F.shelf (Y (u i))).support=_; rw [he]; exact Seat.spread_move ..
  change F.table (Y (u i)) U=_; rw [he]; change F.dataF _ (((Seat.move p x) (Y i).1).view U)=_; rw [Seat.view_move]; rfl
variable {F B}
lemma authentic {c : ℕ→ℝ} (h : F.Fair B c) (H:F.Nulls) (g : G.Simple) (hn : 4≤n.val): (F.coffee A).RegularFamily B := by
  have hr (i : Cycle n) : B.Regular (F.shelf i).support (F.table i):=Seat.regular _ (h.regular _)
  have hi (i : Cycle n) (hi : Nonwrapping (F.shelf i).support (F.shelf i).site) : ∀ u v, IsAffineDirection (F.shelf i).site u→ IsAffineDirection (F.shelf i).site v→ logHessian (F.table i) u v=0 := by
    apply affine_zero (hr _); intro u
    exact (Seat.hessian _ g (h.regular i.2) hi hn u u).trans (H.gone _ (Seat.unwrapped _ hi) _ _ ((LinearJet.isAffine _).2 ⟨_,rfl⟩) ((LinearJet.isAffine _).2 ⟨_,rfl⟩))
  refine ⟨fun i=> hr (numbering _ i),fun i=> ?_,fun i=>hi (numbering _ i)⟩
  let j:=numbering (Cycle n) i
  change F.dataF j.2 (pull j.1.1 j.1.2 1)= 0; rw [pull_one_field]; exact H.one j.2

def cost (B : BudgetPoint) := turnFee B*(Fintype.card Signed:ℝ)
lemma costP (B : BudgetPoint) : 0 ≤ cost B := mul_nonneg (turnFee_pos _).le (Nat.cast_nonneg _)

-- ℕ rows only, path tail landed
lemma totals {p : ℕ → Support n} {f:ℕ→ℝ} {c : ℝ} (hf : SumBudget (fun i=> B.mass (p i) (f i)) c) :
    ∀ o : Site n, SumBudget (fun i : Cycle n=> if i.1.2=o then B.mass (i.1.spread (p i.2)) (turnFee B*f i.2) else 0) (cost B*c):= by
  intro o
  have hh:0≤c:=Cost.nonneg hf
  rw [cost,mul_comm (turnFee B),mul_assoc]; apply Cost.product (f:=fun i:Seat n=> if i.2=o then turnFee B*c else 0)
  · refine Cost.product (Cost.finite (α:=Signed) _ (mul_nonneg (turnFee_pos _).le hh)) (fun i=>⟨fun j=>?_,Summable.of_finite,?_⟩)
    · dsimp only; split; exact mul_nonneg (turnFee_pos _).le hh; rfl
    rw [tsum_fintype]; simp
  intro i; by_cases hx: i.2=o
  · simpa only [if_pos hx,BudgetPoint.mass,Seat.visit_count,mul_left_comm (turnFee B)] using Cost.scale hf _ (turnFee_pos B).le
  simpa only [if_neg hx] using (show SumBudget (fun _:ℕ=> (0:ℝ)) 0 from Push.Local.sumBudget_zero le_rfl)

abbrev wages (c : ℕ→ℝ) (B : BudgetPoint) (i : ℕ) : ℝ:= turnFee B*c (numbering (Cycle n) i).2 -- implicit n
lemma economics {c : ℕ→ ℝ} {b : ℝ} (h : F.Fair B c) (H : SumBudget (fun i=> B.mass (F.footprint i) (c i)) b):
    (F.coffee A).EBound B (cost B*b) := by
  refine ⟨fun i=>wages (n:=n) c B i,fun i=>?_,fun o=> ?_⟩
  · let z:= numbering (Cycle n) i; exact Seat.sup z.1 (h.regular z.2) (h.charge z.2)
  exact Cost.equiv (numbering _) (totals H o)

lemma layer_test {g : ℕ→Pot G n} (F : Frame G n) (B : BudgetPoint) (U) (h : ∀ V,Summable fun i=> g i V)
    (he : ∀ i V, masked B.threshold (F.footprint i) (F.dataF i) V = factor*g i V) : (F.coffee A).additive B U=layer g U:= by
  rw [layer_total g U h]
  let X (j:Cycle n):= factor*g j.2 (j.1.view U)
  refine (tsum_congr (fun i=> show _ = X (numbering _ i) from ?_)).trans ((numbering (Cycle n)).tsum_eq X)
  let j:= numbering (Cycle n) i
  change masked B.threshold (j.1.spread _) (F.dataF j.2 ∘ j.1.view) U=_
  rw [Seat.distribute]; exact he j.2 (j.1.view U)
end Frame
variable {σ C Y a e : ℝ} {B : BudgetPoint}

lemma wax {f g : ℕ→ℝ} (hf : ∀ i,0≤f i) (hx : ℕ→Prop) (he : ∀ i,hx i → a*(f i)≤g i) {X : ℕ→Support n} (hb : 0<a)
    (h : SumBudget (fun i=>B.mass (X i) (g i)) C) :
    SumBudget (fun i=>B.mass (X i) (if hx i then f i else 0)) (a⁻¹*C):= by
  refine Cost.mono (Cost.scale h a⁻¹ (inv_nonneg.mpr hb.le)) (fun i=>mul_nonneg (Real.exp_pos _).le ?_) (fun i=>?_)
  · split; exact hf _; exact le_rfl
  split; next hv=>
    rw [← div_eq_inv_mul]; apply (le_div_iff₀ hb).mpr; unfold BudgetPoint.mass; rw [mul_comm _ a, mul_left_comm]; exact mul_le_mul_of_nonneg_left (he _ hv) (Real.exp_pos _).le
  unfold BudgetPoint.mass; rw [mul_zero]; exact mul_nonneg (inv_nonneg.mpr hb.le) (h.1 _)
end YM.Comparison.Density.Render
