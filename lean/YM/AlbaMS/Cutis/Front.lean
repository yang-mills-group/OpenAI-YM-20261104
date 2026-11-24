import YM.AlbaMS.Cutis.Vax
/-!
# inversion matrices. all real full-torus base indices, attach colors after.

Goal relation to piece Eq. Supports any Side. Edge-base reversal lattice
includes staggering. Show on scalar + harmonic. No ellipticity estimate on
quotient to propagate comparisons, only committed exact expressions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable {X E:Type*}[Fintype X]
def veil (P:Token X): Matrix X X ℝ:= Matrix.of fun x y=> if P.σ x=y then 1 else 0
namespace TokenF
variable (P:Token X)
omit [Fintype X] in
lemma symmetry : (veil P)ᵀ=veil P:=by ext x y; simp only [Matrix.transpose_apply,veil,Matrix.of_apply]; simp [show P.σ x=y ↔ P.σ y=x by constructor <;> rintro rfl <;>apply P.invol]
lemma left (M:Matrix X E ℝ)(x i): (veil P*M) x i=M (P.σ x) i:=by simp [Matrix.mul_apply,veil,ite_mul]
lemma right (M:Matrix E X ℝ)(x i): (M*veil P) i x=M i (P.σ x):=by nth_rw 1 [← symmetry P, ← Matrix.transpose_transpose M]; rw [← Matrix.transpose_mul]; exact left .. -- need sheet rfl
lemma alters [DecidableEq X] : veil P*veil P=1:=by ext x y; rw [left]; simp [veil,P.invol x, Matrix.one_apply]
end TokenF
variable (n : Side) (i:Axis)
def flow : Cell n:= veil (silver n)
def aura : Dir n:= - veil (copper n)
lemma flow_t : (flow n)ᵀ=flow n:= TokenF.symmetry _
lemma aura_t : (aura n)ᵀ=aura n:=by rw [aura,transpose_neg, TokenF.symmetry]
lemma aura_aura : aura n *aura n=1:=by rw [aura, neg_mul_neg]; exact TokenF.alters _
lemma flow_flow : flow n*flow n=1:= TokenF.alters _
lemma flow_left (P:Matrix (Vtx n) E ℝ)(x i):(flow n*P) x i=P (-x) i:= TokenF.left ..
lemma flow_right (P:Matrix E (Vtx n) ℝ)(i x): (P*flow n) i x=P i (-x):= TokenF.right ..
lemma aura_left (P:Matrix (Arm n) E ℝ)(x i): (aura n * P) x i= -P ((copper n).σ x) i:=by rw [aura,Matrix.neg_mul, Matrix.neg_apply,TokenF.left]
lemma aura_right (P:Matrix E (Arm n) ℝ)(i x): (P * aura n) i x= -P i ((copper n).σ x):=by rw [aura,Matrix.mul_neg, Matrix.neg_apply,TokenF.right]
lemma high_mean : aura n * pump n (mean n)= -pump n (mean n):=by
  ext ⟨x,i⟩ ⟨y,j⟩; rw [aura_left]; rfl
lemma low_mean : flow n*mean n=mean n:=by ext i j; exact flow_left ..
lemma mean_low : mean n*flow n=mean n:=by ext i j; exact flow_right ..
lemma aura_bound : aura n * bound n= bound n * flow n:= by
  ext ⟨x,i⟩ y; rw [aura_left,flow_right]; change - bound n (-x-step i,i) y=_; simp only [pa, sub_add_cancel]; rw [show -x-step i=-(x+step i) by abel]; simp only [neg_eq_iff_eq_neg,neg_sub]
lemma boundT : flow n*(bound n)ᵀ=(bound n)ᵀ*aura n:=by nth_rw 1 [← flow_t]; nth_rw 1 [← aura_t]; rw [← transpose_mul, ← transpose_mul, aura_bound]
lemma lap_f : flow n*lap n=lap n*flow n:=by rw [← q_sc, ← Matrix.mul_assoc, boundT,Matrix.mul_assoc, aura_bound, Matrix.mul_assoc]
lemma green_f : flow n*green n=green n*flow n:=by
  let H:=lap n+mean n; have he:H*flow n=flow n*H:=by simp only [H,Matrix.add_mul, Matrix.mul_add, lap_f,mean_low,low_mean];
  have hh:flow n*H⁻¹=H⁻¹*flow n:=by
    nth_rw 1 [← Matrix.one_mul (flow n)]; rw [← Matrix.nonsing_inv_mul H (massive_det n)]; simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc H, he, Matrix.mul_assoc, Matrix.mul_nonsing_inv H (massive_det n), Matrix.mul_one]
  unfold green; rw [Matrix.sub_mul,Matrix.mul_sub,mean_low,low_mean]; exact congr_arg (·-mean n) hh
-- lift by staggering shifts.
lemma reflected (P:Cell n)(ht:Commute (flow n) P)(hp:∀ i,Commute (del n i) P): aura n * pump n P=pump n P* aura n:=by
  have h (x y:Vtx n) (i:Axis) : P (-x-step i) y=P x (-y-step i):=by
    have hz: Commute (limo n (step i)) P:=by rw [show limo n (step i)=del n i+1 by unfold del; abel]; exact (hp i).add_left (Commute.one_left _)
    have hh (x y:Vtx n) : P (x+step i) y=P x (y-step i):= by rw [← limo_left n P (step i) x,← limo_right n P (step i) x, hz.eq]; -- indexes need pass
    have hr x y : P (-x) y=P x (-y):=by rw [← flow_left n P x,← flow_right n P x, ht.eq]
    rw [show -x-step i=-(x+step i) by abel, hr,hh] -- fix
  ext ⟨x,i⟩ ⟨y,j⟩; rw [aura_left,aura_right]; by_cases he:i=j<;> simp [pump,chip,he,copper,h]
lemma LL : aura n * L n=L n*aura n:=reflected n _ (green_f n) (fun i=>(green_del n i).symm)
lemma aura_mono : aura n * mono n=mono n*aura n:=by
  unfold mono; rw [Matrix.mul_sub, Matrix.sub_mul, reflected n _ (lap_f n) (fun i=>(commute_lap n i).symm), ← Matrix.mul_assoc (aura n), aura_bound, Matrix.mul_assoc, boundT, Matrix.mul_assoc]
lemma UU : aura n * U n=U n* flow n:=by unfold U; rw [← Matrix.mul_assoc, LL, Matrix.mul_assoc,aura_bound,Matrix.mul_assoc]
lemma WW : aura n * W n=W n*aura n:=by exact Commute.mul_right (show Commute (aura n) (L n * mono n) from Commute.mul_right (LL n) (aura_mono n)) (LL n)
end YM.MSBar.Cutis.Winter
