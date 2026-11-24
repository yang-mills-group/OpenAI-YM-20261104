import YM.AllOrder.Ink.Canvas
import Mathlib.Data.Set.Finite.List
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {ι:Type}
structure Field (α : Type) where
 Ty : Type
 fee : Ty → ℝ
 slip : Ty → Slip (Point α)
namespace Field
variable (A : Field α)
def price (A: Field α)(σ:ℝ)(i:A.Ty):ℝ:= Real.exp (σ*meter (A.slip i))* |A.fee i|
structure Good (A : Field α)(σ C:ℝ)(k:ℕ): Prop where
 length : ∀ i, (A.slip i).length ≤ k
 pay : SumBudget (A.price σ) C
def site (n:Side)(z:Site n) : rule α n→ℝ := fun x=> ∑' i, A.fee i*invoice z (A.slip i) x
def table (n:Side): rule α n→ℝ:= ∑ z:Site n,A.site n z
omit [Fintype α] in
lemma table_apply (x:rule α n) : A.table n x=∑ z:Site n,A.site n z x:= by rw [table,Finset.sum_apply]
omit [Fintype α] in
lemma price_nonneg (r:ℝ)(i:A.Ty): 0≤A.price r i:= by unfold price; positivity
omit [Fintype α] in
lemma Good.nonneg {A:Field α} (h:A.Good a C k):0≤C:=budget_nonneg h.pay
omit [Fintype α] in
lemma Good.debt {A:Field α} (h:A.Good a C k)(hb:b ≤ a)(hc:C ≤ D)(H:k≤N) : A.Good b D N:= by
 refine ⟨fun i=>(h.length i).trans H,(sumBudget_mono h.pay (A.price_nonneg _) (fun i=>?_) hc)⟩; unfold price; gcongr
omit [Fintype α] in
lemma Good.bare {A:Field α}(h:A.Good a C k)(hb:0≤a): SumBudget (fun i=> |A.fee i|) C:= by rw [← show A.price 0=fun i=> |A.fee i| from funext fun i=>by simp [price]]; exact (h.debt hb le_rfl le_rfl).pay
lemma frame_cost {ι:Type} [Fintype ι] (L:Slip ι): Fire.Prices L.length 1 (fun x:ι→ℝ=> paid x L):= by
 induction L with
 | nil=>exact (price_const (show |(1:ℝ)|≤1 from (abs_one).le) 0)
 | cons x l ih=>
    let A:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : ι=>ℝ) x; have he:Prices 1 1 (A: (ι→ℝ)→ℝ):= ⟨zero_le_one,Rank.line A,fun u=> by change |u x|≤_; rw [pow_one,one_mul]; exact (norm_le_pi_norm u x).trans (le_add_of_nonneg_left zero_le_one) ⟩
    simpa only [one_mul,Nat.add_comm 1 l.length] using! price_mul he ih
lemma ticket (z:Site n) (S:Slip (Point α)) : Fire.Prices S.length 1 (invoice z S):= by
 simpa only [List.length_map] using! frame_cost (S.map (stood z)) --  using frame_cost (S.map (stood z))
lemma Good.earns {A:Field α}(h:A.Good a C k)(hb:0≤a)(z:Site n) (x:rule α n) : SumBudget (fun i=> ‖A.fee i*invoice z (A.slip i) x‖) (roi x^k * C) := by
 apply budget_mono (budget_scale (show 0 ≤ roi x^k by dsimp [roi]; positivity) (h.bare hb)) (fun i => norm_nonneg _) ; intro i; have he:= Prices.up (h.length i) (ticket z (A.slip i)); have hi:=he.2.2 x; rw [one_mul] at hi; rw [Real.norm_eq_abs,abs_mul,mul_comm (roi x^k)]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
lemma Good.posRank {A:Field α}(h:A.Good a C k)(z:Site n)(i:A.Ty):Rank (rule α n) k (invoice z (A.slip i)):= (ticket ..).2.1.up (h.length i)
-- compression repeated `atoms` into torus uses only finite set. Needs smoothness of ℝ→Rank not Lin; use linear probe `f∈RankPart` submodule. construct lemma parameter op F→G independent. use repeatedly sum linear within rank.
open Classical
omit [Fintype α]
abbrev Frame (α : Type) (k:ℕ):= {l:List α//l.length≤ k}
instance {α:Type} [Finite α]: Fintype (Frame α k) := (List.finite_length_le α k).fintype
abbrev nub (S: Frame α k):=S.val -- type def Set? ↑Set? fix
variable {A : Field α} (h:A.Good a C k) (hb:0 ≤ a) (z : Site n)
def figure (i : A.Ty): Frame (Leaf n α) k := ⟨(A.slip i).map (stood z),by simp [h.length i]⟩
variable [Fintype ι]
omit [Fintype α] in
lemma cash (hb:0≤a) (h:A.Good a C k): Summable A.fee := Summable.of_norm (show Summable (fun i=> ‖A.fee i‖) from (h.bare hb).2.1)
lemma bookwise {κ:Type}(u : κ→ℝ)(v : ι→ℝ)(e : κ→ι)(h:Summable u) : HasSum (fun i:κ=>u i*v (e i)) (∑ i:ι,(∑' j,if i=e j then u j else 0)*v i) := by
 let f j i:= if j=e i then u i else 0; have he(j:ι):Summable (f j):=(h.indicator {i|j=e i}).congr (fun i=>by simp [Set.indicator,f]);
 refine ((hasSum_sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset ι))=> (he i).hasSum.mul_right (v i))).congr_fun ?_); intro b; simp only [f,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] -- order sum;
end Field
end YM.AllOrder.Ink
