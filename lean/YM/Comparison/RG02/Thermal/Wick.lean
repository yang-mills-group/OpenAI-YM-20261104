import YM.Comparison.RG02.Thermal.Layers
import YM.Comparison.RG02.Order.Second
import YM.Comparison.RG02.Bulk.Spur
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Thermal
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Affinity Gaussian Bulk RG Wilson Exterior YM.Work.F05
open PertExtension.Series

private lemma jet1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f:X→ℝ) (x:X) : Radial.expsum (Radial.layers f) 1 1 x= - Assembly.jet f 3 x := by
   norm_num only [Radial.expsum,Radial.layers,Finset.sum_range_succ, Finset.sum_range_zero, Zone.TaylorPow,Zone.mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,if_true,if_false,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Nat.factorial, ← Assembly.jet_eq, Nat.reduceSub, Nat.reduceAdd,neg_add_cancel]

private lemma jet2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f:X→ℝ) (x:X) : Radial.expsum (Radial.layers f) 2 2 x= -Assembly.jet f 4 x+(Assembly.jet f 3 x)^2/2 := by
   norm_num only [Radial.expsum,Radial.layers,Finset.sum_range_succ, Finset.sum_range_zero, Zone.TaylorPow,Zone.mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,if_true,if_false,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Nat.factorial,← Assembly.jet_eq,Nat.reduceSub,Nat.reduceAdd,neg_add_cancel]; ring

private theorem mean_value (f : (I→ℝ) → ℝ) (b:ℝ) (Q:Gaussian.Table I) (hQ : Q.PosDef) (hf : ∀ v, f v + f (-v)=2*b) (hi : Integrable f (cloud Q)) : ∫ v,f v ∂cloud Q=b := by
   -- proof via under_cloud then volume. works nonnegative or not.
   let A x:= Real.exp (-(force Q x/2)); let p x:= A x • f x
   have h m : (fun x=> Real.exp ((force Q x)/2) • (A x • m x))=(m:(I→ℝ)→ℝ):= by funext x; unfold A; rw [smul_smul,← Real.exp_add, add_neg_cancel,Real.exp_zero, one_smul]
   obtain ⟨hp,H⟩:= under_cloud hQ p
   -- trim coercion
   change _ ↔ Integrable (fun x=> Real.exp _ • (A x • f x)) (cloud Q) at hp
   rw [h f] at hp
   simp_rw [p, h f] at H -- syntactic? lambda expansion under let.
   obtain ⟨he,HH⟩:= under_cloud hQ (fun x=>A x • b)
   rw [h (fun _=> b)] at he HH
   let N : Vec I ≃ᵐ Vec I := (Homeomorph.neg _).toMeasurableEquiv; let μ:= (volume:Measure (Vec I))
   have hn : MeasurePreserving N μ μ := Measure.measurePreserving_neg ..
   have ht (x:Vec I): A (-x)=A x := by simp [A,force,Matrix.mulVec_neg]
   have hz : p+p ∘ N=(2:ℝ) • (fun x=> A x * b):=by funext x; unfold p; change A x*f x + A (-x) * f (-x)=2*(A x*b);rw [ht, ← _root_.mul_add, hf]; ring
   have hx := congrArg (fun q:Vec I→ℝ=>∫ v, q v) hz
   simp only [Pi.add_apply] at hx; rw [integral_add (hp.mpr hi) ((hn.integrable_comp_emb N.measurableEmbedding).mpr (hp.mpr hi))] at hx  -- comp signature
   rw [show (∫ x,(p ∘ N) x)= ∫ x, p x from hn.integral_comp N.measurableEmbedding p] at hx
   have hp' : (∫ x, p x) = _ := H
   simp_rw [hp',show ((2:ℝ) • fun x=> A x * b) = fun x=> (2:ℝ)* (A x • b) from rfl, integral_const_mul,HH, integral_const, Measure.real_def, measure_univ] at hx
   have hh:= coat_pos hQ; simp only [ENNReal.toReal_one,smul_eq_mul] at hx; exact mul_left_cancel₀ hh.ne' (by linarith)

namespace Wick
open Laplace
variable {c f : Side} {S : StepData c f} {P : PathData G} {p : Clip} {O : ChartRatio G}
variable (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (W : Colors R G f) (hW : W.Standard)
local notation "I'"=> Precision.Key F G
local notation "X"=> fieldDir G c 1
local notation "Λ'"=> Precision.Key F G→ℝ
local notation "Z"=> House X I'
local notation "T"=> Fix.vibe K F t
local notation "Q"=> K.covariance F t
local notation "Aϑ"=> Pull.blown K F t T W
local notation "ν"=> Gaussian.cloud (K.covariance F t)
variable [Fintype V] {r : ℕ}
local notation "C"=>Layers.forecast K F t

-- st, - tested in positive exponent. station/stiffness Thermal sign.
def paid (x:X) (n:ℕ) (v: Λ') := Radial.expsum (Radial.layers Aϑ) n n (1,x,v)
include hW
lemma cheque (x:X) (n:ℕ) (hn:n≤r) : let f := paid K F t W x n
   Integrable f ν ∧ Order.Second.lit n (Bulk.Fk K F t W x r)= Complex.ofReal (∫ v,f v ∂ν) := by
   intro f'
   rw [Pull.port hW.1 K F t T x r, Order.Second.grade]
   let p := Pull.painted K F T W; let q := W.power; let T':Z:= (1,x,0)
   have he := Assembly.gather T' (reach X) q p Aϑ Q (K.symm F t) (K.positive F t) R.quiet (pick r n); rw [picked _ hn] at he
   have hv:= Assembly.order_read T' (reach X) q p Aϑ Q (K.symm F t) (K.positive F t) R.quiet hn
   have ho : Assembly.insideMoment T' (reach X) q p Aϑ R.quiet n=(fun v=> (f' v:ℂ)) := by
      funext v; rw [Assembly.insideMoment,Bulk.clear]; congr 1; exact congrArg (Radial.expsum (Radial.layers Aϑ) n n) (facing x v)
   rw [ho] at he hv
   refine ⟨he.1.re,?_⟩; unfold Pull.forecast; exact hv.trans integral_ofReal

lemma pays_first (x:X) (h : 1≤r): Order.Second.lit 1 (Fk K F t W x r) = -(C x 1 : ℂ) := by
   obtain ⟨hi,hA⟩:= cheque K F t W hW x 1 h
   rw [hA,mean_value _ (-(C x 1)) _ (K.positive F t) ?_ hi, Complex.ofReal_neg]; intro v
   unfold paid; rw [jet1,jet1,Layers.first K F t W hW x v,Layers.first K F t W hW x (-v), Layers.blanker K F t W hW]; ring

/-- offset of second interacting `vacuum` tested log coefficient: all marked moments are
    **divided by** this same vacuum. It's field-dependent; the remainder here is the extensive
    constant, no claim on its size. Used before kappa kinetic matching/reset. -/
lemma sq (x:X) (h : 2≤r) : Order.Second.lit 2 (logVac (Fk K F t W x r)) = -(C x 2:ℂ)+ Order.Second.lit 2 (logVac (Fk K F t W 0 r)) := by
   let X' := paid K F t W x 2; let Y := paid K F t W 0 2; let s:= C x 1; let c:= C x 2
   have he : ∀ v:Λ', (X'-Y) v + (X'-Y) (-v)=2*(-c+s^2/2) := by
      intro v; dsimp only [Pi.sub_apply]; unfold X' Y paid; simp_rw [jet2]
      have hu := Layers.second K F t W hW x v
      rw [Layers.first K F t W hW x v, Layers.first K F t W hW x (-v), Layers.blanker K F t W hW]; unfold s c; linear_combination -hu
   obtain ⟨hi,hx⟩:= cheque K F t W hW x 2 h; obtain ⟨hj,hy⟩:= cheque K F t W hW 0 2 h; have ht:= mean_value _ _ _ (K.positive F t) he (hi.sub hj : Integrable (X'-Y) ν)
   simp only [Pi.sub_apply] at ht; rw [integral_sub (f:=X') hi (g:=Y) hj] at ht
   have h₁ : 1≤r:=by omega
   have hz : C 0 1=0:=by unfold Layers.forecast; simp only [Clipper.empty _ (by decide : 2+1≠0) (Layers.base K F t), Clipper.empty 1 (by decide),add_zero]
   rw [Order.Second.offset_two (fk_sym K F t W x r) (fk_unit ..) h, Order.Second.offset_two (fk_sym K F t W 0 r) (fk_unit ..) h, hx, hy, pays_first K F t W hW x h₁, pays_first K F t W hW 0 h₁,hz];
   rw [sub_eq_iff_eq_add] at ht; change (↑(∫ v,X' v ∂ν) : ℂ)-_= _+ ((↑(∫ v,Y v ∂ν):ℂ)-_); rw [ht]; unfold s c; push_cast; ring

lemma pays_first_log (x:X) (h : 1≤r) : Order.Second.lit 1 (logVac (Fk K F t W x r))= -(C x 1:ℂ) := by rw [Order.Second.offset_one (fk_sym ..) (fk_unit ..) h, pays_first K F t W hW x h]
end Wick
end YM.Comparison.RG02.Thermal
