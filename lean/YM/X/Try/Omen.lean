import YM.X.Try.Glory
/-! # uniform-Ψ completion: actual orbit face C expression in the normalization, stems shift locally recolors but disappears in Stone. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set Asymptotics Gauge
open Source PertExtension LatticePT Braid Gauss ProjectorNext.Calibration
open Stems hiding X
open Stems.Log
open Jet hiding Word
open scoped Topology ContDiff BigOperators Pointwise Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {k:ℕ} {u v:ℝ→G.El}{p r t:G.Color}
local notation "B"=> G.mat
local notation "J"=> G.colorMat
local notation "A"=> Atom G
lemma lm {V W:Type*} [NormedAddCommGroup V][NormedAddCommGroup W][NormedSpace ℝ V][NormedSpace ℝ W](F:V→L[ℝ] W){f:ℝ→V}(hf:ContDiffAt ℝ ω f 0): iteratedDeriv k (F ∘ f) 0= F (iteratedDeriv k f 0):= by
    unfold iteratedDeriv; rw [F.iteratedFDeriv_comp_left hf le_top] -- inspect
    rfl
lemma roots_inv (h:Roots u p r): Roots u⁻¹ (-p) (-r):= by
   let L:= (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap; let f:= B ∘ u; have he: B ∘ u⁻¹=L ∘ f:= funext fun i=> G.mat_inv (u i)
   refine ⟨inv_eq_one.mpr h.lights, he.symm ▸ L.contDiff.contDiffAt.comp 0 h.matC, ?_,?_ ⟩
   · rw [he]; apply HasDerivAt.congr_deriv (L.hasFDerivAt.comp_hasDerivAt 0 h.matL); change star (J _)=_; rw [G.colorMat_skew,map_neg]
   rw [he,show iteratedDeriv 2 (L ∘ f) 0=L (iteratedDeriv 2 f 0) from lm L h.matC,h.matP]; change star (_+_)=_; simp [G.colorMat_skew]
lemma shift_self (v:G.Color): Log.shift v v=0:= by unfold Log.shift; rw [show G.ad v v=0 from G.colorMat_injective (by simp),smul_zero]
lemma shift_pinch (v:G.Color): Log.shift v (-v)=0:= by unfold Log.shift; rw [map_neg, smul_neg,show ((1/2:ℝ) • _)=_ from shift_self v,neg_zero]
lemma roots_conj (h:Roots u p r)(hh:Roots v 0 t): Roots (u*v*u⁻¹) 0 t:= by
    have he:= (h.times hh).times (roots_inv h); have hz: Log.shift p 0=0:= by simp [Log.shift]
    simp only [hz,add_zero,add_neg_cancel,shift_pinch] at he; convert he using 1; abel -- [hz,add_zero,add_neg_cancel, shift_pinch, add_zero] at he; convert he using 1; abel
lemma roots_walk (l:Walk)(x:Cover)(a:Brush G): ∃ p r:G.Color, Roots (fun t:ℝ=> travel (posit (t•a)) x l) p r:= by
   induction l generalizing x with
   | nil=> use 0,0; have he:= Roots.Exponent (G:=G) 0; simp only [smul_zero] at he; exact (show (fun t:ℝ=>G.lieExp (0:G.Color))= (fun t=>travel (posit (t•a)) x []) from funext fun t=> by apply G.mat_injective; simp [travel]) ▸ he
   | cons d l IH=>
      obtain ⟨p,r,H⟩:= IH (x+d.vec); let f(t:ℝ):=d.read (posit (t•a)) x; have hh : ∃ p r:G.Color, Roots f p r:= by
         unfold f Step.read; cases he:d.neg <;> simp only [he, Bool.false_eq_true, ↓reduceIte]; · exact ⟨_,0, Roots.Exponent (a (d.used x))⟩
         exact ⟨_,_,roots_inv (Roots.Exponent (a (d.used x))) ⟩
      obtain ⟨p',r',hh⟩:=hh; exact ⟨_,_,hh.times H⟩
lemma log_fire (a b:G.Color): Log.sub a b a b=G.ad a b:= by
    have he:= shift_self b; have hh:= shift_skew b a; have hk:= shift_self a; unfold Log.sub; unfold Log.shift at *; simp only [map_neg,map_add, smul_add, smul_neg, LinearMap.add_apply] at *;
    rw [add_sub_cancel_left,hk,he,hh,neg_zero,add_zero,zero_add,neg_neg, ← add_smul, show 1/2+1/2=(1:ℝ) by norm_num, one_smul] -- rewrites
lemma port_c (a:G.Mat): G.projectColor ((1/2:ℝ) • (a-star a))=G.projectColor ((1/2:ℝ) • (a-star a)):= rfl
private def projectM : G.Mat→L[ℝ] G.Color:= G.projectColor.toContinuousLinearMap.comp ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ G.Mat)-(starL' ℝ).toContinuousLinearMap))
lemma routeZ (x:G.El): G.curvature x=projectM (G.mat x) := by rw [Gauge.curvature,G.mat_inv]; rfl
lemma hence (h:Roots u 0 r): iteratedDeriv 2 (G.curvature ∘ u) 0= (2:ℝ) • r:= by
    rw [show G.curvature ∘ u=projectM ∘ (B ∘ u) from funext fun x=> routeZ _,show iteratedDeriv 2 ((projectM (G:=G)) ∘ (B ∘ u)) 0=(projectM (G:=G)) (iteratedDeriv 2 (B ∘ u) 0) from lm _ h.matC,h.matP, map_zero]; simp only [mul_zero,add_zero,map_smul]; change (2:ℝ) • G.projectColor ((1/2:ℝ) • (J r-star (J r)))= _; rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ,smul_smul]; norm_num
lemma hence_ok (h:Roots u p r): ContDiffAt ℝ ω (G.curvature ∘ u) 0:= by rw [show G.curvature ∘ u=projectM ∘ (B ∘ u) from funext fun x=> routeZ _]; exact projectM.contDiff.contDiffAt.comp _ h.matC
local notation "H"=> (⊤: Submodule ℝ (Reed.Fan G))
def SlotV (x:Atom G)(U:CoverConfig G):= ((x.1.eval U) x.2)
lemma equipped (x:Atom G): Small G (SlotV x):= (Small.slot x.1).comp (EuclideanSpace.proj (𝕜:=ℝ) x.2|>.contDiff) -- may specify f
local notation "Θ"=> G.ColorIndex
-- antisym output
noncomputable def ff (i j k:Θ): ℝ:= G.ad (tan j) (tan k) i
lemma aspect (u v z:G.Color) : Inner.inner ℝ u (G.ad v z)= ∑ i:Θ,∑ j:Θ,∑ k:Θ,ff i j k * u i * v j * z k:= by
    conv_lhs=> rw [restore_tan u,restore_tan v,restore_tan z];
    unfold ff; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,sum_inner,inner_sum,Finset.smul_sum, real_inner_smul_left,real_inner_smul_right]; unfold tan; simp_rw [EuclideanSpace.basisFun_inner]
    conv_lhs=> rw [Finset.sum_comm]
    conv_rhs=> rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; ring
lemma axel (u v:G.Color)(k:Θ): G.ad u v k=∑ i:Θ,∑ j:Θ,ff k i j*u i*v j:= by
    have hh:= aspect (tan k) u v; unfold tan at hh; rw [EuclideanSpace.basisFun_inner, Finset.sum_eq_single k] at hh; simpa [EuclideanSpace.single_apply, Pi.single_apply] using hh
    all_goals simp_all [EuclideanSpace.single_apply, Pi.single_apply, ne_comm]
-- ∗completion polynomial∗
def glove (x:CoverC G) : Curly G:= ∑ i:Θ, ∑ j:Θ, (ff x.2 i j:ℂ) • (X ((0,x.1.val.1),i) * X ((0,x.1.val.2),j))
lemma sting (a:Brush G)(x:CoverC G): snap a (glove x)=(↑(G.ad (a (0,x.1.val.1)) (a (0,x.1.val.2)) x.2 ):ℂ):= by
    rw [axel]; unfold glove; simp only [snap,map_sum,map_smul,map_mul,aeval_X, Complex.ofReal_sum,Complex.ofReal_mul]; unfold Stems.text; simp [smul_eq_mul,mul_assoc]
lemma forecast (x:Atom G) (a:Axis→G.Color): someJ (along (SlotV x) (fun i:Pin=>a i.2)) 2= G.ad (a x.1.plaq.val.1) (a x.1.plaq.val.2) x.2:= by
    let t:Brush G:= fun i=> a i.2; let f:= fun (r:ℝ)=> travel (posit (r•t)) 0 x.1.walk; let p:Face ℤ:= (x.1.offset,x.1.plaq); let g (r:ℝ):= faceValue (posit (r•t)) p; let X:= p.2.val.1; let Y:= p.2.val.2; let u:= f*g*f⁻¹; let T:= G.ad (a X) (a Y)
    obtain ⟨w,y,h⟩:= roots_walk x.1.walk 0 t; have hv : Roots u 0 T:= roots_conj (u:=f) h (v:=g) (by rw [show T=Log.fire t p.1 X Y from (log_fire ..).symm,← show Stems.curl t p.1 X Y=0 from (by change a X+a Y-a Y-a X=0; abel)]; exact Log.fixture p t)
    let L:= (EuclideanSpace.proj (𝕜:=ℝ) x.2); rw [someJ, show along (SlotV x) t= L ∘ (G.curvature ∘ u) from ?_,lm _ (hence_ok hv),hence hv, map_smul]; norm_num [smul_smul]; change _= L T; ring
    ext1 r; exact congr_arg (fun p:G.Color=> p x.2) (G.curvature_conjugate (f r) (g r)) |>.symm
lemma slot_stone (x:Atom G): Stone H 2 (mark (SlotV x) (equipped x) 2) (glove (drop x)):= by
    have he : pressP (mark (SlotV x) (equipped x) 2)=glove (drop x):= by
       refine snap_ext (fun a=>?_); rw [sting,press_eval,mark_test]
       apply congr_arg; exact forecast x (fun i=> a (0,i))
    rw [← he]; exact pressureP _ (markHC (SlotV x) _)
end YM.PositionX.Tri
