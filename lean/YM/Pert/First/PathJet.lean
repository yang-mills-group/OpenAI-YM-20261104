import YM.Pert.First.FirstWeight
import Mathlib.Analysis.SpecialFunctions.Exponential
/-! Two derivatives along log-potential rays before physical h scaling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 440000
namespace YM.Pert.First
open Orb Lattice Filter Matrix Function Topology NormedSpace
open scoped Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {N : Side}
/-- Constant term one, ordered log derivatives with the necessary commutator at second order. -/
def defect (v w : G.Color) : G.Mat := (G.colorMat v)^2 + G.colorMat w
lemma defect_add (v w a b : G.Color) : defect (v+w) (a+b+(G.ad v) w) = defect v a + (G.colorMat v * G.colorMat w + G.colorMat v * G.colorMat w) + defect w b := by simp only [defect,map_add,G.colorMat_ad]; noncomm_ring
structure Tried (p : ℝ→G.Mat) (v w : G.Color) : Prop where
  value_eq : p 0 = 1
  slope_eq : ∃ z : ℝ→G.Mat, z 0=G.colorMat v ∧ (∀ t, HasDerivAt p (z t) t) ∧ HasDerivAt z (defect v w) 0
variable {v w a b : G.Color} {p q : ℝ→G.Mat}
lemma Tried.second (hp : Tried p v a) : iteratedDeriv 2 p 0= defect v a := by
  obtain ⟨r,r0,h,h'⟩ := hp.slope_eq
  have e := funext (fun t=> (h t).deriv)
  rw [iteratedDeriv_succ,iteratedDeriv_one,e,h'.deriv]
lemma Tried.product (hp : Tried p v a) (hq : Tried q w b) : Tried (fun t=> p t*q t) (v+w) (a+b+G.ad v w) := by
  refine ⟨show _ by simp [hp.value_eq,hq.value_eq],?_⟩
  obtain ⟨z,hz,hd,hzz⟩ := hp.slope_eq
  obtain ⟨y,hy,he,hyy⟩ := hq.slope_eq
  refine ⟨fun t=>z t * q t + p t * y t, show _ by simp [hz,hy,hq.value_eq,hp.value_eq],fun t=>(hd t).mul (he t),?_⟩
  convert! ((hzz.mul (he 0)).add ((hd 0).mul hyy)) using 1
  rw [hz,hy,hq.value_eq,hp.value_eq,defect_add]; noncomm_ring

def glow (v : G.Color) (t : ℝ) := G.mat (G.lieExp (t • v))
lemma glow_tried : Tried (glow v) v 0 := by
  let M := G.colorMat v
  have he t : HasDerivAt (glow v) (glow v t * M) t := by rw [show glow v=(fun t : ℝ=>NormedSpace.exp (t • M)) from funext fun _ => (G.mat_lieExp _).trans (by rw [G.colorMat.map_smul])];  exact hasDerivAt_exp_smul_const M t
  have hf : glow v 0=1 := by simp [glow]
  refine ⟨hf,_,?_,he,?_⟩
  · simp [M,hf]
  simpa [defect,pow_two,hf] using! ((he 0).mul_const M)

def square_path (v w a b : G.Color) (t : ℝ):= glow v t * glow w t * glow a t * glow b t
def linearSq (v w a b : G.Color) := ((v+w)+a)+b
def bracketSq (v w a b : G.Color) := G.ad v w + G.ad v a + G.ad v b + G.ad w a + G.ad w b + G.ad a b
lemma square_tried : Tried (square_path v w a b) (linearSq v w a b) (bracketSq v w a b) := by
  unfold square_path linearSq bracketSq
  have he := ((glow_tried (v:=v) |>.product (glow_tried (v:=w))).product (glow_tried (v:=a))).product (glow_tried (v:=b))
  convert! he using 1; simp only [map_add,LinearMap.add_apply,add_zero,zero_add]; abel

def shadowL (G : Gauge) : G.Mat →L[ℝ] G.Mat := (1/2:ℝ) • (ContinuousLinearMap.id ℝ _ -(starL ℝ).toContinuousLinearMap)
def recoverL (G : Gauge) : G.Mat →L[ℝ] G.Color := G.projectColor.toContinuousLinearMap ∘L shadowL G
lemma decode_defect (v a : G.Color) : recoverL G (defect v a)=a := by
  change G.projectColor ((1/2:ℝ) • (defect v a - star (defect v a))) = _
  have h : 1/2+(1/2:ℝ)=1 := by norm_num
  unfold defect; rw [star_add,star_pow,G.colorMat_skew,G.colorMat_skew,sq,sq,neg_mul_neg,add_sub_add_left_eq_sub,sub_neg_eq_add,smul_add,←add_smul,h,one_smul,G.project_colorMat]
lemma Tried.decode_second (hp : Tried p v b) : iteratedDeriv 2 (recoverL G ∘ p) 0 = b := by
  obtain ⟨z,hz,he,hh⟩:=hp.slope_eq
  let L := recoverL G
  have e : deriv (L ∘ p) = L ∘ z := funext fun t=> (L.hasFDerivAt.comp_hasDerivAt t (he t)).deriv
  change iteratedDeriv 2 (L ∘ p) 0 = _; rw [iteratedDeriv_succ,iteratedDeriv_one,e]
  exact (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) hh).deriv.trans (decode_defect v b)
lemma recover_group (u : G.El) : G.curvature u = recoverL G (G.mat u) := congrArg (fun z=> G.projectColor ((1/2:ℝ) • (G.mat u-z))) (G.mat_inv u)
end YM.Pert.First
