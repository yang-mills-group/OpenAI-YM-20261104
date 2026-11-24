import YM.AllOrder.Laplace.Facet
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
local notation "Ω" => ℝ × Y

lemma sqpay (a:ℝ) : HasFDerivAt (𝕜:=ℝ) (fun x:Ω=> a*x.1^2) 0 0:= by have hh:= ((show HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ _ _) (0:Ω) from hasFDerivAt_fst).pow 2).const_mul a; simpa using! hh
lemma sq_jet (t:ℝ)(u:Ω): jet (fun x:Ω=> t*x.1^2) 2 u=t*u.1^2:=by
 let f (x:ℝ):=t*(x^2 * u.1^2)
 rw [homogeneous_derivative _ u 2 (by fun_prop)]
 have h : iteratedDeriv 2 f 0=2*(t*u.1^2):=by
    unfold f; rw [show (fun x:ℝ=>t*(x^2 * u.1^2))=(fun x:ℝ=> x^2)*(fun _=> t*u.1^2) from funext (fun x=>by rw [Pi.mul_apply]; ring),iteratedDeriv_mul (by fun_prop) (by fun_prop)]; norm_num [iteratedDeriv_fun_pow_zero,Finset.sum_range_succ,Nat.factorial]
 rw [show (fun r:ℝ => t*(r • u).1^2)=f from funext (fun r=>by simp [mul_pow,f]), h]; norm_num [Nat.factorial]; ring
variable {F:X × Y→ℝ} {K:ℝ×(X × Y)→ℝ} {A : ℝ×(X×Y)→ℝ} {ρ:X→Y} {P:ℝ→X}{W:ℝ→Y}{ζ:ℝ}
-- hard includes analytics order ≥1, K amplitude not necessarily >0 until using symmetry. Extra germ leaves all joint total<=2 jets except scalar offsets too (e.g. loop constant canceled at input). P0=0 coarse.
structure Treaty (F:X×Y→ℝ)(ρ:X→Y)(A K:ℝ×(X×Y)→ℝ):Prop where
   steer : Steered F ρ
   activity : ContDiffAt ℝ ω A 0
   rank : ∀ n:ℕ,n ≤ 2→ jet A n=jet (F ∘ Prod.snd) n
   ample : ContDiffAt ℝ ω K 0

structure NextTo (ρ:X→Y)(P:ℝ→X)(W:ℝ→Y):Prop where
   p0 : P 0=0
   cont : ContDiffAt ℝ ω P 0
   w0 : W 0=0
   progress : ContDiffAt ℝ ω W 0
   bank x : fderiv ℝ W 0 x=fderiv ℝ ρ 0 (fderiv ℝ P 0 x)
lemma belong (h:Steered F ρ)(hp: P 0=0)(hf:ContDiffAt ℝ ω P 0):NextTo ρ P (ρ∘P):=
   ⟨hp,hf,(by rw [comp_apply,hp,h.map0]),(hp.symm ▸ h.shape).comp _ hf,hp ▸ fun x=>by rw [fderiv_comp _ _ _,hp]; rfl; exact hp.symm ▸ h.shape.differentiableAt (by simp); exact hf.differentiableAt (by simp)⟩
lemma flat_belong (h:Steered F ρ)(hp:P 0=0)(hf:ContDiffAt ℝ ω P 0):NextTo ρ P (⇑(fderiv ℝ ρ 0 ∘L fderiv ℝ P 0)):= ⟨hp,hf,map_zero _, (fderiv ℝ ρ 0 ∘L fderiv ℝ P 0).contDiff.contDiffAt, fun x=> by rw [ContinuousLinearMap.fderiv]; rfl⟩ -- warning h

def tone (P:ℝ→X)(W:ℝ→Y)(x: Ω): ℝ×(X×Y):= (x.1,P x.1,W x.1+x.2)
def lance (P:ℝ→X)(W:ℝ→Y)(x:Ω) : ℝ×(X×Y):= (x.1,fderiv ℝ P 0 x.1, fderiv ℝ W 0 x.1+x.2)
-- q unscaled extra

def prepare (A:ℝ×(X×Y)→ℝ)(P:ℝ→X)(W:ℝ→Y)(ζ:ℝ):Ω→ℝ := A∘ tone P W+fun z=>ζ*z.1^2
variable (h:Treaty F ρ A K)(hp:NextTo ρ P W)
include h hp
local notation "x0"=> curvature F (fderiv ℝ P 0 1) (fderiv ℝ W 0 1)
omit h in
lemma tone0 : tone P W 0=0:= by unfold tone; simp [hp.w0,hp.p0]
omit h in
lemma fluid : ContDiffAt ℝ ω (tone P W) 0 := contDiffAt_fst.prodMk ((hp.cont.comp (f:=Prod.fst) (0:Ω) contDiffAt_fst).prodMk ((hp.progress.comp (f:=Prod.fst) (0:Ω) contDiffAt_fst).add contDiffAt_snd))
omit h in
lemma lance_at : ∀ x, fderiv ℝ (tone P W) 0 x=lance P W x := by
 let L:= ContinuousLinearMap.fst ℝ ℝ Y; let M:= ((fderiv ℝ W 0)∘L L)+ContinuousLinearMap.snd ℝ ℝ Y
 have he : HasFDerivAt (P∘ L) ((fderiv ℝ P 0) ∘L L) (0:Ω) := (hp.cont.differentiableAt (by simp)).hasFDerivAt.comp (0:Ω) L.hasFDerivAt
 have hh : HasFDerivAt (W∘ L) ((fderiv ℝ W 0)∘L L) (0:Ω) := (hp.progress.differentiableAt (by simp)).hasFDerivAt.comp (0:Ω) L.hasFDerivAt
 have hn : HasFDerivAt (tone P W) (L.prod (((fderiv ℝ P 0) ∘L L).prod M)) 0 := L.hasFDerivAt.prodMk (he.prodMk (hh.add ((ContinuousLinearMap.snd ℝ ℝ Y).hasFDerivAt)))
 intro i; exact DFunLike.congr_fun hn.fderiv i
omit hp in
lemma treaty_roots : A 0=0 ∧ fderiv ℝ A 0=0:= by
  have hu: HasFDerivAt (𝕜:=ℝ) (F ∘ Prod.snd (α:=ℝ)) 0 0:= by
     let L:=ContinuousLinearMap.snd ℝ ℝ (X×Y)
     simpa only [h.steer.quiet, ContinuousLinearMap.zero_comp] using! (((show (HasFDerivAt F (fderiv ℝ F 0) (L 0)) from ((h.steer.hard.differentiableAt (by simp)).hasFDerivAt))).comp 0 L.hasFDerivAt)
  constructor; · calc _ = jet A 0 0:= (jet_zero ..).symm
                      _ = _ := by rw [h.rank 0 (by omega),jet_zero]; exact h.steer.root
  apply ContinuousLinearMap.ext; intro x; rw [← zero_first,h.rank 1 (by omega),zero_first, hu.fderiv]

lemma scaffold (x : Ω) : jet (prepare A P W ζ) 2 x=(x0+ζ)*x.1^2+curvature F 0 x.2:= by
   let y:=fderiv ℝ P 0 1; let z:= fderiv ℝ W 0 1
   have he:= h.steer
   unfold prepare; rw [jet_add ((show ContDiffAt ℝ ω A (tone P W 0) from (tone0 hp).symm ▸ h.activity).comp _ (fluid hp)) (by fun_prop),sq_jet, jet_two_C (fluid hp) h.activity (tone0 hp) (treaty_roots h).2,h.rank 2 (by omega),lance_at hp,jet_two_C contDiffAt_snd he.hard (rfl) he.quiet]
   have hv : HasFDerivAt (@Prod.snd ℝ (X×Y)) (ContinuousLinearMap.snd ℝ _ _) (0:ℝ×(X×Y)):=hasFDerivAt_snd
   rw [hv.fderiv]
   change curvature F (fderiv ℝ P 0 x.1) (fderiv ℝ W 0 x.1+x.2)+_=_
   rw [hp.bank,he.gauge, ← hp.bank]; have hq : (fderiv ℝ P 0 x.1,fderiv ℝ W 0 x.1)=x.1 • (y,z) := by
      rw [Prod.smul_mk,← map_smul (fderiv ℝ P _),← map_smul (fderiv ℝ W _),smul_eq_mul,mul_one]
   unfold curvature; rw [hq,jet_smul]; unfold y z; ring
variable [FiniteDimensional ℝ Y]
lemma approved (he:0<x0+ζ): Cylinder (prepare A P W ζ) (K ∘ tone P W):= by
 have ht:= treaty_roots h; refine ⟨⟨(((show ContDiffAt ℝ ω A (tone P W 0) from (tone0 hp).symm ▸ h.activity).comp _ (fluid hp)).add (by fun_prop)).of_le le_top,?_,?_⟩,((show ContDiffAt ℝ ω K (tone P W 0) from (tone0 hp).symm ▸ h.ample).comp _ (fluid hp)).of_le le_top,quadratic_min _ ?_⟩
 · simp [prepare,tone0 hp,ht.1]
 · let a:= ζ; have hh: HasFDerivAt (𝕜:=ℝ) (A∘ tone P W) 0 0:= by simpa only [ContinuousLinearMap.zero_comp] using ((tone0 hp).symm ▸ (show HasFDerivAt A (0) (0:ℝ×(X×Y)) from ht.2 ▸ (h.activity.differentiableAt (by simp)).hasFDerivAt)).comp 0 ((fluid hp).differentiableAt (by simp)).hasFDerivAt
   intro x; rw [zero_first, show fderiv ℝ (prepare A P W ζ) 0=_ from (hh.add (sqpay ζ)).fderiv]; simp
 intro x hx; rw [scaffold h hp]; by_cases hf:x.2=0
 · have hw : x.1≠0:=fun hi=> hx (Prod.ext hi hf)
   rw [hf,show curvature F 0 0=0 by change jet F 2 0=0; rw [jet_two_H]; simp,add_zero]; positivity
 exact add_pos_of_nonneg_of_pos (by positivity) (h.steer.stand _ hf)
end YM.AllOrder.Laplace
