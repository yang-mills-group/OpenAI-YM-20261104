import YM.Comparison.Density.Render.Frame

/-!
Third and higher vacuum logarithmic packets in the *actual representation*.
This is Group nonlinear proof even on winding. Retain full orientation
and expose exact complementary tails at any finite path cutoff with their
own addresses. Precision requested powers need exp-tail schedule receipt.
Mass weighted by true support including any auxiliary data included before
rooting. Here no extra test address on vacuum, larger support versions
can charge the cover expansion as in duo. Don't assume analytic truncated
Σ links is reconstruction.
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

section Cut
variable (n : Side) (F : ℕ→ Atom G k) (a : ℝ) (h : ℕ→Prop)

def recipe (a : ℝ) (h : ℕ→Prop) (n : ℕ) : ℝ := if h n then factor*a else 0

def rack : Frame G n := {
  footprint := fun i=> (F i).footprint (0:Site n)
  pivot i := mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩
  dataF i := recipe a h i • fun U=> (F i).unmasked U 0 }

def postW (m : ℕ) (i : ℕ) := m≤ (F i).length
def plainSeries (F:ℕ→Atom G k) (a:ℝ) (n : Side) (q:ℕ→Prop) (B : BudgetPoint) (i : ℕ) (U : Config G n) :=
    if q i then a*(F i).placed B U 0 else 0
variable {n} {B : BudgetPoint} {σ C : ℝ}

lemma subsidy (h : SumBudget (fun i=> (F i).budget σ) C) (hσ : 0<σ) (B : BudgetPoint) (p : ℕ→Prop) (U : Config G n):
    Summable fun i=> plainSeries F a n p B i U := by
  have he:=((PathData.atom_dominated F B (0:Site n) hσ h).summable U).mul_left a |>.norm
  refine Summable.of_norm (he.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>?_))
  unfold plainSeries; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
lemma bandFits (hf : ∀ i,(F i).Invariant) (B : BudgetPoint):
    Frame.Fair (rack n F a h) B fun i=> |recipe a h i| *Wages.price B (F i):=
  ⟨fun i=>AnalyticBridge.CouplingShape.reg_scale _ (Derivs.canonical_regular _ _ B (hf i)),fun i=> AnalyticBridge.CouplingShape.sup_scale _ (Wages.total B (F i) _)⟩
lemma bandNull (hs : 3≤k): Frame.Nulls (rack n F a h):= by
  have hk:1≤k:=by omega
  haveI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  constructor
  · intro i; change _*(F i).unmasked (1:Config G n) 0=_; simp [Atom.unmasked,Atom.poly,transported,roll,unitTravel,G.curvature_unit,Nat.ne_zero_iff_zero_lt.mpr hk]
  intro i hu x y _ _; unfold logHessian
  let t:=recipe a h i; let f:Directions G n→ℝ:= fun A=> (F i).unmasked (increment 1 A) 0
  have hf : ContDiffAt ℝ 2 f 0:= by exact (reserved (k:=2) (F i) 0 (by simp : ‖(0:Directions G n)‖ ≤ 1)).smooth
  change iteratedFDeriv ℝ 2 (t • f) 0 _=0; rw [iteratedFDeriv_const_smul_apply hf,show iteratedFDeriv ℝ 2 f 0=0 from valuation (F i) 2 hs _]; simp

lemma whole_test (A : Activities G n) (a : ℝ) (B : BudgetPoint) (h : ℕ→Prop) (hs : SumBudget (fun i=> (F i).budget σ) C) (hσ : 0 < σ) (U) :
    ((rack n F a h).coffee A).additive B U= layer (plainSeries F a n h B) U:= by
  refine Frame.layer_test A (rack n F a h) B U (subsidy F a hs hσ B h) fun i V=> ?_
  unfold rack recipe plainSeries Atom.placed; dsimp only
  split
  next hi=> change masked _ _ (fun U=> (factor*a)* _) V = _; rw [mask_mul]; ring
  next hi=> change masked _ _ (fun U=> (0:ℝ)* _) V = _; rw [mask_mul]; ring

-- full & ≥path stages on same support (no slack from dropping exponent).
lemma main_price (A : Activities G n) (hf : ∀ i,(F i).Invariant) (hs : SumBudget (fun i=> (F i).budget σ) C) (hσ : 0<σ) (hv : B.supportExponent / B.B ≤ σ/4) :
    ((rack n F a h).coffee A).EBound B (Frame.cost B * (|factor*a| *(fund G B.power B.order k B.supportExponent σ * B.threshold^k*C))):= by
  apply Frame.economics A (bandFits F a h hf B)
  refine Cost.mono (Cost.scale (Wages.ticket B σ C hσ hv F hs (0:Site n)) _ (abs_nonneg (factor*a))) (fun i=> ?_) (fun i=>?_)
  · exact mul_nonneg (Real.exp_pos _).le (((bandFits F a h hf (n:=n) B).charge _).1)
  unfold BudgetPoint.mass; rw [mul_left_comm |factor*a|]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hp (i) := (Wages.fin B (F i) (0:Site n)).nonneg
  refine mul_le_mul ?_ (le_mul_of_one_le_left (hp i) (Real.one_le_exp (mul_nonneg (by positivity : 0 ≤ σ/4) (by positivity)))) (hp i) (abs_nonneg _)
  unfold recipe; split; rfl; rw [abs_zero]; exact abs_nonneg _
lemma remaining (A : Activities G n) (hf : ∀ i,(F i).Invariant) (hs : SumBudget (fun i=> (F i).budget σ) C) (hσ : 0<σ) (hv : B.supportExponent / B.B ≤ σ/4) (x : ℕ) :
    let p:=postW F x
    ((rack n F a p).coffee A).EBound B (Frame.cost B * (|factor*a| *(Real.exp ((σ/4)*x))⁻¹ * (fund G B.power B.order k B.supportExponent σ * B.threshold^k*C))):= by
  intro p; apply Frame.economics A (bandFits F a p hf B)
  let K:= fun i=> Wages.price B (F i)
  have hp (i) := (Wages.fin B (F i) (0:Site n)).nonneg
  have ht : ∀ i,p i → Real.exp ((σ/4)*x)*K i ≤ toll B σ (F i):=by
    refine fun i he=> mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ σ/4))) (hp i)
    exact_mod_cast he
  have hL:= wax hp p ht (Real.exp_pos _) (Wages.ticket B σ C hσ hv F hs (0:Site n))
  rw [mul_assoc |factor*a|]; refine Cost.mono (Cost.scale hL |factor*a| (abs_nonneg _)) (fun i=> ?_) (fun i=> ?_)
  · exact mul_nonneg (Real.exp_pos _).le (((bandFits F a p hf (n:=n) B).charge _).1)
  · unfold recipe BudgetPoint.mass; dsimp only [rack]; split_ifs; rw [mul_left_comm]
    rw [abs_zero,zero_mul,mul_zero,mul_zero]

-- exact complement and downstream E addressing. Independent witness not here.
lemma dual (F : ℕ→ Atom G k) (hf:∀ i,(F i).Invariant) (A : Activities G n) (m : ℕ) (hr : SumBudget (fun i=> (F i).budget σ) C) (hσ : 0 < σ) (hv : B.supportExponent / B.B ≤ σ/4) (U) :
    let E:=fun q=> (rack n F a q).coffee A
    (E (fun _=>True)).additive B U=(weave (E (fun i=> ¬ postW F m i)) (E (postW F m))).additive B U:= by
  intro E
  let f(q:ℕ→Prop):=plainSeries F a n q B
  have hp: (E (fun i=> ¬postW F m i)).EBound B _ := main_price F a _ A hf hr hσ hv
  have hq: (E (postW F m)).EBound B _ := main_price F a _ A hf hr hσ hv
  have he q:(E q).additive B U=layer (f q) U:= whole_test F A a B q hr hσ U
  rw [weave_summed hp hq,he,he,he,← layer_combine (f:=f (fun i=> ¬postW F m i)) (g:=f (postW F m)) (subsidy F a hr hσ B _) (subsidy F a hr hσ B _)]
  refine congrArg (layer · U) (funext fun i=>funext fun V=>?_); by_cases ht:postW F m i <;> simp [f,plainSeries,ht]
end Cut
end YM.Comparison.Density.Render
