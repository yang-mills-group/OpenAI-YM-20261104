import YM.QuadraticLocal.Manifold

/-!
For using the raw Lyric stamps at the unchanged address table. (In the second merger we'll let
marked terms also combine with changed vacuum slips.) Same-slot exact K rule. No disjointness claim
within a column. `T` passive, permits all products/kernels to use common bounds. Apply later to
full Census slots including extra/error controls simultaneously.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 Ovens Fusion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace SameSlot
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V : Type*} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T ι : Type*} {w : V→ ℝ} {a b : ℝ} {B : ℕ}

lemma sumHit (p : ι→ℕ) (X : ℕ→Support n) (f:ι→ℝ)
    (_hF : ∀ i,0 ≤ f i) (hH : Hit (X ∘ p) B f a b) :
    Hit X B (fun i=> ∑' j:{j // p j=i}, f j.val) a b := by
  intro x; let g (j:ι) := if x∈ X (p j) then f j*Real.exp (a*coverNumber B (X (p j))) else 0; have he : SumBudget g b := hH x; let F:=g ∘ Equiv.sigmaFiberEquiv p; let f' i:= ∑' j : {j // p j=i}, F ⟨i,j⟩
  have ht(i:ℕ): (if x∈ X i then (∑' j:{j // p j=i}, f j.val)*Real.exp (a*coverNumber B (X i)) else 0)=f' i:= by
    unfold f'; simp_rw [F,g,Function.comp_apply]; change _=∑' j:{j // p j=i}, if x∈ X (p j.val) then f j.val* Real.exp (a*coverNumber B (X (p j.val))) else 0; simp_rw [show ∀ j:{j // p j=i}, p j.val=i from fun j=>j.property]; split; rw [tsum_mul_right]; rw [tsum_zero]
  rw [funext ht]; have hF': Summable F := (Equiv.sigmaFiberEquiv p).summable_iff.mpr he.2.1
  refine ⟨fun i=> tsum_nonneg (fun j=> he.1 _), hF'.sigma, ?_⟩; unfold f'; rw [← hF'.tsum_sigma, show ∑' i,F i=∑' i,g i from (Equiv.sigmaFiberEquiv p).tsum_eq g]; exact he.2.2

lemma coveredSum {x y:ι → Poly R} (h:∀ i, Width.Covered (x i) (y i)) (hx:Summable x) (hy: Summable y): Width.Covered (∑' i,x i) (∑' i,y i):= by
  intro v; have hz : Continuous fun z:Poly R=>(z.part v).re:= Complex.continuous_re.comp (Poly.part_cont v)
  have he : Tendsto (fun s:Finset ι => ‖(∑ i∈s,x i).part v‖) atTop (𝓝 (‖(∑' i,x i).part v‖)):= ((Poly.part_cont v).norm).continuousAt.tendsto.comp hx.hasSum
  constructor
  · refine le_of_tendsto_of_tendsto' he (hz.continuousAt.tendsto.comp hy.hasSum) (fun s => ?_)
    change _≤ ((∑ i∈s,y i).part v).re; rw [Poly.part_sum,Poly.part_sum,Complex.re_sum]; exact (norm_sum_le ..).trans (sum_le_sum fun i _=> (h i v).1)
  let f i := (y i).part v; have ht : (∑' i,y i).part v=∑' i,f i:=Poly.share hy v; rw [ht, show (∑' i,f i).im= ∑' i,(f i).im from Complex.imCLM.map_tsum ((hy.hasSum.map (Poly.get v) (Poly.part_cont v)).summable)]; simp_rw [show ∀ i, (f i).im=0 from fun i=> (h i v).2]; exact tsum_zero

lemma sumLocalCharge [Countable ι] {f:ι → Config G n → Poly R} {D:Support n} (hF: ∀ i, Width.LocalCharge p o D (f i)) (h:∀ U,Summable fun i=> f i U) : Width.LocalCharge p o D (fun U=> ∑' i,f i U):= by
  refine ⟨fun a U=> tsum_congr fun i=> (hF i).gauge a U, Measurable.tsum fun i=> (hF i).borel,fun U W hx ht=> tsum_congr fun i=>(hF i).reads U W hx ht,?_⟩
  intro U i hi j hj; by_contra hq; apply hi; rw [Poly.share (h _)]; exact (tsum_congr (g:=fun _=>0) fun q=> (show (f q U).part i=0 from not_ne_iff.mp (fun hh=> hq ((hF q).carry _ _ hh _ hj)))).trans tsum_zero

structure Group (f:ι→ℕ) (p:BudgetPoint) (X:ℕ→ForcedAddress G n) (R:Census V) (o:V→Site n) (T:Type*) where
  val : ι → T → Config G n → Poly R
  property i t : Width.LocalCharge p o (X (f i)).support (val i t)
  permit i t U : val i t U ≠ 0 → (X (f i)).eligible p.threshold U

namespace Group
variable {f:ι→ℕ} {A : ℕ→ ForcedAddress G n} {F : Code G n}
variable (X : Group f p A R o T)
structure Price (w : V→ℝ) (B : ℕ) (a b : ℝ) : Prop where
  cost : ∃ g:ι→ Poly R, (∀ i t U, Width.Covered (X.val i t U) (g i)) ∧
    Hit (fun i=> (A (f i)).support) B (fun i=> Poly.price w (g i)) a b

def column (t:T) (i : ℕ)(U : Config G n):= ∑' j:{j // f j=i},X.val j.val t U
lemma Price.quality (h:X.Price w B a b) (ha:0≤a) (hw:∀ i,0<w i) (U : Config G n) (t:T) (i : ℕ): Summable (fun j:{j // f j=i}=> X.val j.val t U) := by
  obtain ⟨g,hg,hH⟩:=h.cost
  have he:= (Letters.Frame.from_hit B a b _ (fun (i:ι)=> (A (f i)).inventory_ne.mono (A (f i)).inventory_sup) (fun i=> Poly.nonnegative hw (g i)) ha hH)
  exact (show Summable (fun i=> X.val i t U) from (Poly.budgeted hw he.2.1 fun i=> (hg i t U).reprice _ hw).1).comp_injective Subtype.val_injective

variable [Countable ι]
-- quiet must tie same vacuum, not inferred from equality of aggregate K estimate.
def hard (h:X.Price w B a b) (ha:0≤a) (hw:∀ i,0<w i)
    (hq:∀ i U t,(X.column t i U).part R.quiet=(F i U:ℂ)): Hard T p A F o R where
    hard:= X.column
    locality t i:=sumLocalCharge (fun j:{j //f j=i} => by
      have hz:= X.property j.val t; rw [show A (f j.val)=A i from congr_arg A j.property] at hz; exact hz) (fun U=> h.quality X ha hw U t i)
    charged t i U hv:= Classical.byContradiction (fun hs=>hv ( by
      unfold column
      refine (tsum_congr (g:=fun _=>0) (fun j=> not_ne_iff.mp (fun hn=>hs ?_))).trans tsum_zero
      rw [← show A (f j.val)=A i from congr_arg A j.property]; exact X.permit _ t _ hn))
    quiet t i U := hq i U t

lemma pays (h:X.Price w B a b) (ha:0≤a)(hw:∀ i,0<w i)
    (hq:∀ i U t,(X.column t i U).part R.quiet=(F i U:ℂ)): (X.hard h ha hw hq).Paid w B a b := by
  obtain ⟨g,hg,hH⟩:= h.cost; have he:= (Letters.Frame.from_hit B a b _ (fun (i:ι)=> (A (f i)).inventory_ne.mono (A (f i)).inventory_sup) (fun i=> Poly.nonnegative hw (g i)) ha hH); let f' i := ∑' j:{j // f j=i}, g j.val; have hf i:= Poly.budgeted hw (he.2.1.comp_injective (show Injective (Subtype.val (p:=fun j=> f j=i)) from Subtype.val_injective)) (fun (j:{j // f j=i})=> le_refl (Poly.price w (g j.val)))
  refine ⟨f',fun i t U=> coveredSum (fun j:{j // f j=i} => hg j.val t U) (h.quality X ha hw U t i) (hf i).1, fun i=>?_⟩
  apply budget_mono (sumHit f (fun j=>(A j).support) _ (fun i=> Poly.nonnegative hw _) hH i)
  · intro j; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_nonneg _); rfl
  intro j; split; exact mul_le_mul_of_nonneg_right (hf j).2 (Real.exp_pos _).le; rfl
end Group
end SameSlot
end YM.QuadraticLocal
