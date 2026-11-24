import YM.MSbar.TreeOPE.Powers
import YM.Next.MAXWELL.Derives
import YM.MSbar.Tree.Profile

/-!
# Script for curvature slot transport

Using real probes on four-dimensional free jets (exact leading order,
no dim-dependent recursion in this OPE lemma). Prove joint linear &
color covariance behavior of legs before substitution in formal Gaussian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Set Filter Asymptotics
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank Normal Tree
open scoped ContDiff Topology BigOperators Classical InnerProductSpace

variable {G : Gauge} {k l j : ℕ}
lemma lengths (u v : Slot G) (x y t : E4) (r : ℝ) (hp : x≠y) (hr:0<r) :
    (r:ℂ)^(scaleW u+scaleW v)*entry u v (t+r • x) (t+r • y)=entry u v x y:= by
  have hx:x-y∈away:=sub_ne_zero.mpr hp; have hz:r • (x-y)∈away:= smul_ne_zero hr.ne' hx
  simp_rw [entry, add_sub_add_left_eq_sub, ← smul_sub,← compiled_four 1 _ _ _ hz,← compiled_four 1 _ _ _ hx]
  unfold compiled; simp_rw [Finset.mul_sum,line_zero 1 _ _ _ hx,line_zero 1 _ _ _ hz]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
  rw [mul_smul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_mul]; congr 1
  congr 1; rw [pow_add]
  exact Prayer.grown (native a) (native b) hr _ hx

def reify (p : Probe G k) : Slot G→₀ℂ:= ∑ i : Fin (legDim G k), Finsupp.single ⟨k,i⟩ (p (frame G k i):ℂ)
lemma reified (p : Probe G k) : glyph (reify p)=symbol k p:= by unfold reify symbol; rw [map_sum]; apply Finset.sum_congr rfl; intro a _; rw [glyph,Finsupp.linearCombination_single, MvPolynomial.C_mul']
lemma at_leg (p : Probe G k) (q : Probe G j) (x y : E4) (h : x≠y): linearCombination ℂ
    (fun s : Slot G => (↑(K (coordinateLeg s) q x y):ℂ)) (reify p)=↑(K p q x y):= by
  have hp:= probe_expansion p; unfold reify; rw [_root_.map_sum]; simp_rw [Finsupp.linearCombination_single,smul_eq_mul]
  have hq:x-y∈away:=sub_ne_zero.mpr h; let A:= pairing (G:=G) (j:=k) (l:=j) hq
  change (∑ i:Fin (legDim G k),(↑(p (frame G k i)):ℂ)* ↑(A (coordinateLeg ⟨k,i⟩) q))= ↑(A p q); conv_rhs => rw [hp,_root_.map_sum];
  simp_rw [LinearMap.sum_apply, map_smul, LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]; rfl
lemma at_leg' (p : Probe G k) (q : Probe G j) (x y : E4) (h : x≠y): linearCombination ℂ
    (fun s : Slot G => (↑(K p (coordinateLeg s) x y):ℂ)) (reify q)=↑(K p q x y):= by
  simp_rw [K_symmetric p _ h]; exact at_leg q p y x (Ne.symm h)

/- direct using linearity from leg representation. color-transform p.comp. -/
private def pigmentLeg (g : G.El) (k): Probe G k →ₗ[ℝ] Probe G k:= LinearMap.lcomp ℝ ℝ (castFace g k)

private def basisL (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ
private def tone (g : G.El) (i : G.ColorIndex) := G.adjoint g⁻¹ (basisL G i)
private lemma tone_acts (g : G.El) (i : G.ColorIndex) (x : G.Color) : (G.adjoint g x) i=∑ b, tone g i b * x b:= by
  rw [← EuclideanSpace.basisFun_inner]
  let L : G.Color →ₗᵢ[ℝ] G.Color:= ⟨G.adjoint g,G.norm_adjoint g⟩
  rw [show (EuclideanSpace.basisFun G.ColorIndex ℝ) i=L (tone g i) by change _=G.adjoint g (tone g i); rw [tone, ← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]; rfl]
  change ⟪L (tone g i), L x⟫_ℝ = _; rw [show _= _ from L.inner_map_map (tone g i) x, real_inner_comm]; rfl
private lemma toner (x y : G.ColorIndex) (g : G.El) : (∑ b, tone g x b * tone g y b)=(if x=y then 1 else 0):= by
  let L : G.Color →ₗᵢ[ℝ] G.Color:= ⟨G.adjoint g⁻¹,G.norm_adjoint g⁻¹⟩
  change ⟪L (basisL G y), L (basisL G x)⟫_ℝ = _; rw [show _=_ from L.inner_map_map (basisL G y) (basisL G x)]; unfold basisL; rw [real_inner_comm,EuclideanSpace.basisFun_inner]; simp
private lemma pigment_align (x : Fin k→E4) (g : G.El) (a : G.ColorIndex) (i j : Axis) : pigmentLeg g k (leg x a i j)=∑ b, tone g a b • leg x b i j:= by
  ext1 p; rw [LinearMap.sum_apply]; exact tone_acts g a _
lemma K_tone (p : Probe G k) (q : Probe G j) (x y : E4) (h : x≠y) (g : G.El) : K (p.comp (castFace g k)) (q.comp (castFace g j)) x y=K p q x y:= by
  have hK:x-y∈away:=sub_ne_zero.mpr h; let X:=pairing (G:=G) (j:=k) (l:=j) hK
  change X (pigmentLeg g k p) (pigmentLeg g j q) = X p q
  induction p using leg_probe_induction generalizing q with
  | vars u c i m =>
    induction q using leg_probe_induction with
    | vars v d a n=>
      rw [pigment_align,pigment_align, map_sum]; unfold X
      simp only [LinearMap.sum_apply,map_sum,map_smul, LinearMap.smul_apply,smul_eq_mul]
      have he c d : (pairing (G:=G) hK) (leg u c i m) (leg v d a n)= _:= raw_mixed _ _ _ _ _ _ _ _ (show x-y≠0 from hK)
      simp_rw [he, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← mul_assoc (tone g d _),← Finset.sum_mul,toner]; split_ifs <;> simp_all
    | zero => simp
    | add i j hi hj=> simp only [map_add,hi,hj]
    | smul t i hi => simp only [map_smul,hi]
  | zero=> simp
  | add a b ha hb=> simp only [map_add,LinearMap.add_apply,ha,hb]
  | smul t a ha=> simp only [map_smul,LinearMap.smul_apply,ha]
end YM.MSbar.OPE

namespace YM.MSbar.OPE
open Function Set Filter Asymptotics
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical InnerProductSpace

variable {G : Gauge} {k l j n : ℕ}
def rows (g : G.El) (i : Slot G) := reify ((coordinateLeg i).comp (castFace g i.fst))
lemma rows_expr (g : G.El) : pigment g= Next.Rank.Normal.exchange (rows g):= by ext1 i; rw [pigment,MvPolynomial.aeval_X, exchange_x]; exact (reified _).symm
private lemma tabs (i j : Fin n) (p q : Slot G→₀ℂ) {x : Points n} (hx : x∈conf n) :
    treats (frameX hx) (p.mapDomain (fun a=>(i,a))) (q.mapDomain (fun b=>(j,b)))=
      linearCombination ℂ (linearCombination ℂ (fun a b=> if i=j then 0 else entry a b (x i) (x j)) p) q := by
  unfold treats; rw [linearCombination_mapDomain, linearCombination_mapDomain]
  congr 2; funext a; simp only [linearCombination_apply,Finsupp.sum, Finset.sum_apply,Function.comp_apply,Pi.smul_apply, frameX]
lemma pigment_frame (g : G.El) {x : Points n} (hx : x∈ conf n): scope (perSlot (fun _=> rows g)) (frameX hx)=frameX hx:= by
  apply Symmetric.ext; funext i j; unfold scope; simp only; rw [perSlot,perSlot,tabs]
  unfold frameX; split <;> rename_i h
  · simp [h,linearCombination_apply,Finsupp.sum]
  simp_rw [if_neg h]
  have hz : x i.1 ≠ x j.1:= (show Injective x.ofLp from hx).ne h
  have hu (v : Slot G) : (linearCombination ℂ (fun a b=> entry (G:=G) a b (x i.1) (x j.1)) (rows g i.2) : Slot G → ℂ) v=
      ↑(K ((coordinateLeg i.2).comp (castFace g _)) (coordinateLeg v) (x i.1) (x j.1)) := by
    rw [← at_leg _ _ (x i.1) _ hz]; simp only [linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply]; rfl
  rw [funext hu,rows, at_leg' _ _ _ _ hz,K_tone _ _ _ _ hz]; rfl

end YM.MSbar.OPE
