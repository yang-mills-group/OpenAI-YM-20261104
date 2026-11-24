import YM.RG11Scheme.Stencil.Flux
import YM.Pert.First.ActionVertex

/-! Explicit bilinear column of first nonlinear curvature and polarized third jet of the weight. Work in literal log potentials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.RG11Scheme.Stencil.Spark
open Filter Function Lattice Set Mesh Pert Pert.First Gauge
open scoped BigOperators Classical
variable {G:Gauge} {X:Type} [AddCommGroup X] [One X]
abbrev stepL (X:Type) := Edge (Four X)
abbrev tensor (X:Type) (G:Gauge) := stepL X → G.Color

def tremor (ε:Four X→G.Color) (x:stepL X) := ε x.1-ε (x.1+step x.2)
def arc (ε:Four X→G.Color) (B:tensor X G) (x:stepL X) := (1/2:ℝ) • G.ad (ε x.1+ε (x.1+step x.2)) (B x)
def adMult {E:Type} [AddCommGroup E][Module ℝ E] (A B:E→ₗ[ℝ]G.Color) : E→ₗ[ℝ] E→ₗ[ℝ] G.Color := LinearMap.mk₂ ℝ (fun x y=> G.ad (A x) (B y)) (fun x y z=>by simp) (fun r x y=>by simp) (fun x y z=>by simp) (fun r x y=>by simp)

variable {D:Type} [AddCommGroup D] [Module ℝ D]
local notation "α" => D →ₗ[ℝ] G.Color

def meld (A B:α) := (1/2:ℝ) • (adMult A B + (adMult A B).flip)
lemma meld_val (A B : α)(x y:D) : meld A B x y = (1/2:ℝ) • (G.ad (A x) (B y)+G.ad (A y) (B x)) := by simp [meld,adMult]
lemma ad_rev (x y:G.Color) : G.ad y x = - G.ad x y := by apply G.colorMat_injective; simp

def blending (A B C Q : α) := meld A B+meld A C+meld A Q+meld B C+meld B Q+meld C Q
lemma blending_same (A B C Q : α) (x:D) : blending A B C Q x x= First.bracketSq (A x) (B x) (C x) (Q x) := by
   have he (p q:α) : meld p q x x=G.ad (p x) (q x):= by rw [meld_val,← two_smul ℝ,smul_smul]; norm_num
   simp_rw [blending,LinearMap.add_apply,he]; rfl
local notation "Δ" => tensor X G
def take (l: stepL X): Δ →ₗ[ℝ] G.Color := LinearMap.proj l

def duo (x:Four X) (i j : Axis) : Δ →ₗ[ℝ] Δ →ₗ[ℝ] G.Color:= blending (take (x,i)) (take (x+step i,j)) (-take (x+step j,i)) (-take (x,j))
lemma dface (x:Four X) (i j) (A:Δ) : duo x i j A A = bracketAt x i j A := blending_same ..
lemma dapply (x:Four X) (i j) (A B:Δ) : duo x i j A B = (1/2:ℝ) • (bracketAt x i j (A+B)-bracketAt x i j A-bracketAt x i j B) := by
   simp_rw [← dface]; rw [map_add]; simp only [LinearMap.add_apply,map_add]
   have he : duo x i j A B=duo x i j B A := by unfold duo blending; simp only [LinearMap.add_apply,meld_val]; abel
   rw [←he]; rw [show (duo x i j A A + duo x i j A B + (duo x i j A B + duo x i j B B) - duo x i j A A - duo x i j B B) = 2 • duo x i j A B from by abel]
   -- 2 smul nsmul
   rw [two_smul,←two_smul ℝ,smul_smul]; norm_num

lemma curl_line (A:Δ)(x:Four X)(i j) : curlAt x i j A = Bare.wideCurl A x i j := by unfold curlAt linearSq Bare.wideCurl Vleft Xleft Vright Xright; abel
lemma peaks_flat (ε:Four X→G.Color)(x:Four X) (i j) : curlAt x i j (tremor ε)=0 := by rw [curl_line]; unfold Bare.wideCurl tremor; rw [add_right_comm x]; abel
lemma key_ward (A:Δ)(ε:Four X→G.Color)(x:Four X)(i j) : duo x i j A (tremor ε)+curlAt x i j (arc ε A)=G.ad (ε x) (curlAt x i j A) := by
  apply G.colorMat_injective
  rw [curl_line,curl_line]; unfold duo blending take; simp only [LinearMap.add_apply, meld_val,LinearMap.proj_apply,LinearMap.neg_apply]
  unfold Bare.wideCurl tremor arc; rw [show x+step j+step i=x+step i+step j by abel]
  simp only [map_add,map_sub, map_smul,map_neg,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.sub_apply,G.colorMat_ad,smul_add,smul_sub,smul_neg]
  module
lemma dflip (x:Four X)(i j)(A B:Δ) : duo x i j B A=duo x i j A B := by unfold duo blending; simp only [LinearMap.add_apply,meld_val]; abel
def vib (x:Four X) (i j:Axis) : Δ →ₗ[ℝ] G.Color := take (x,i)+take (x+step i,j)-take (x,j)-take (x+step j,i)
theorem vib_eq (x:Four X)(i j)(A:Δ) : vib x i j A=curlAt x i j A := by rw [curl_line]; rfl

def vertex (A B C:Δ)(x i j) := if i<j then inner ℝ (curlAt x i j A) (duo x i j B C)+inner ℝ (curlAt x i j B) (duo x i j A C)+inner ℝ (curlAt x i j C) (duo x i j A B) else 0
def surge (A B C:Δ) (x) := ∑ i:Axis,∑ j:Axis,vertex A B C x i j
lemma marked (A:Δ)(x:Four X) : surge A A A x = 3 * ∑ i,∑ j, costVertex x i j A := by
   unfold surge costVertex; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; unfold vertex; simp only [dface]; split_ifs <;> ring
lemma third_ward (A B:Bond G)(ε:Cover→G.Color)(x:Cover): surge A B (gradient ε) x = -(variational A (arc ε B) x + variational B (arc ε A) x) := by
    unfold surge variational; rw [← Finset.sum_add_distrib,←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _;rw [← Finset.sum_add_distrib,←Finset.sum_neg_distrib];apply Finset.sum_congr rfl; intro j _; unfold vertex fee
    split_ifs <;> rename_i hu; swap; · simp
    let u := curlAt x i j A
    let v := curlAt x i j B
    simp_rw [show gradient ε=tremor ε from rfl,peaks_flat, inner_zero_left,add_zero]
    have he (W : Bond G) : curl W x i j=curlAt x i j W:= (curl_line W x i j).symm
    rw [he,he,he,he]; rw [show duo _ _ _ B _=_ from eq_sub_of_add_eq (key_ward B ε x i j),show duo _ _ _ A _=_ from eq_sub_of_add_eq (key_ward A ε x i j), inner_sub_right,inner_sub_right]
    have ht : inner ℝ (curlAt x i j A) (G.ad (ε x) v)= -inner ℝ v (G.ad (ε x) u) := (real_inner_comm ..).trans (G.ad_skew ..)
    rw [ht]; dsimp only [u,v]; abel
end YM.RG11Scheme.Stencil.Spark
