import YM.QuadraticLocal.Sunrise.Picture
/-!
# Material torus cover projection with no root wrapping assumptions
 Charge on post-peak Field; bequest Heat.F.N.Pass even with projected.Carter width.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Focus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push AllOrder.Ink.Money
open scoped BigOperators Topology Classical ContDiff
variable {G: Gauge} {n m:Side} {ι α β:Type}[Fintype α][Fintype β][Fintype ι][DecidableEq ι] (T:Finset ι) (k:ℕ)
variable {a C D:ℝ}
local notation "Λ"=> Focus.Assignment ι k
local notation "J"=> ((α⊕ι))
local notation "U"=> rule (α⊕ι) n
local notation "σ"=> sustain (α:=α) (n:=n)
local notation "mom" i:max=> dayV k ∘ (i:Λ)
variable (F:AllOrder.Ink.Field (α⊕ι))
def emblem : AllOrder.Ink.Field (α⊕ι) where
 Ty:= {i:F.Ty|Depicted T (F.slip i)}
 slip := fun i=> F.slip i.val
 fee := fun i=> F.fee i.val
local notation "Eb"=> emblem T F
variable (h:F.Good a C k)(ht:0≤a)
lemma runs (i:(emblem T F).Ty): Depicted T ((emblem T F).slip i):= i.property
include h ht
lemma scopedT : (emblem T F).Good a C k:= ⟨fun i=> h.length (i.val),sumBudget_subtype _ h.pay⟩ -- name reserved?
lemma plays (x:Site n) : (emblem T F).site n x= lens T k (F.site n x):= by
 funext y; let p (i:F.Ty):= Depicted T (F.slip i); let f(v:rule J n)(i:F.Ty):= F.fee i * invoice x (F.slip i) v; let g(w:Λ)(i:F.Ty):= cap T k w * f ((σ (mom w)) y) i; have hh(i:Λ):Summable (g i):= (h.total ht x _).mul_left _; have he : (Eb).site n x y= ∑' i:F.Ty, if p i then f y i else 0 :=by convert _root_.tsum_subtype {i:F.Ty|p i} (f y) using 1 <;>rfl
 rw [he,billK]; rw [show (∑ w:Λ, cap T k w *F.site n x ((σ (mom w)) y))=∑ w:Λ, ∑' i:F.Ty,g w i from (by unfold g; simp_rw [tsum_mul_left]; rfl),← Summable.tsum_finsetSum (fun i _ => hh i)]; apply tsum_congr; intro i; have hx := invoiceCertified T k (F.slip i) (h.length i) x y; rw [billK] at hx; rw [show ∑ w:Λ,g w i= F.fee i* ∑ w:Λ, cap T k w * invoice x (F.slip i) ((σ (mom w)) y) from ?_,hx]; swap; · rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _=> (mul_left_comm (cap T k w) (F.fee i) _))
 unfold p; split <;> simp only [f, mul_zero]
lemma sends (n:Side): (emblem T F).table n = lens T k (F.table n):= by funext x; rw [Field.table_apply]; simp_rw [plays T k F h ht,billK T k,Field.table_apply, Finset.mul_sum]; exact Finset.sum_comm -- ambiguity?
omit h ht
variable {Ad:Side→Prop}{V:Type}{Γ:V→ℝ}{B: V→Bills (α⊕ι)} {l:ℕ}
-- carries prices in Weight (polynomial) and structure all lengths through Q.IB.Stark.
structure Gift (T:Finset ι){Γ:V→ℝ}(Ad:Side→Prop)(B:V→Bills (α⊕ι))(a:ℝ)(k l:ℕ):Prop where
 transfer : ∃ (F:V→AllOrder.Ink.Field (α⊕ι))(C:V→ℝ)(D:V→ Side→ℝ), CreditF Γ l C ∧ Weight Γ l D ∧ ∀ i,Pert Ad (B i) (F i) a (C i) (D i) k ∧ ∀ j,Depicted T ((F i).slip j)
lemma provided (Hx:0≤a)(hf:License Ad Γ B a k l) : Gift T (Γ:=Γ) Ad (fun i n=> lens T k (B i n)) a k l := by
 obtain ⟨F,C,D,hC,hD,h⟩:=hf; let I:=interest T k; let P(i:V)(n:Side):= I*D i n; have hP : Weight Γ l P:= by simpa only [Nat.zero_add] using (Weight.fixed _ I (asset ..)).times hD;
 refine ⟨⟨(fun i=> emblem T (F i)),C,P,hC,hP,fun i=> ⟨⟨Focus.scopedT T k _ ((h i).1) Hx, fun n hn=>?_⟩,runs T (F i)⟩⟩⟩
 let s:= B i n; let V:=lens T k s-(emblem T (F i)).table n; rw [Focus.sends T k _ (h i|>.1) Hx,← Focus.less T k]; unfold P; rw [mul_assoc]; exact fee T k ((h i).2 n hn) -- fee captured reserved notation?
end YM.QuadraticLocal.Sunrise.Focus
