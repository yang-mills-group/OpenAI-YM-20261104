import YM.SignedWilsonExpansion.TorchE
namespace YM.SignedWilsonExpansion.Heter
/-! Polar ray-torch for the cross derivative on two external momenta. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView
open scoped Classical Topology ContDiff BigOperators
open Energy (plane leg firstE)
section mixed
variable {E L:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   [ NormedAddCommGroup L ][NormedSpace ℝ L]
variable {F H : ℝ×ℝ→E}
abbrev ofXY (a b:ℝ) : ℝ×ℝ:=(a,b)
local notation "Y" => (ℝ×ℝ)
local notation "ν" => ofXY 1 0
local notation "ξ" => ofXY 0 1
def dY (F:Y→E): ℝ→E:= fun x=> deriv (fun y=> F (x,y)) 0
def tooth (F:Y→E): E:= deriv (dY F) 0
def ray_read (F:Y→E)(x:Y) : E:= ((1/2):ℝ) • iteratedDeriv 2 (fun t:ℝ=>F (t • x)) 0

lemma direction (xi:Y)(hp:Differentiable ℝ F)(a:Y)(t:ℝ): HasDerivAt (fun t:ℝ=> F (a+t • xi)) ( (fderiv ℝ F (a+t • xi)) xi ) t:= by
    let u (t:ℝ):= a+t • xi
    apply (hp (u t)|>.hasFDerivAt).comp_hasDerivAt t
    convert ((hasDerivAt_id' t).smul_const xi).const_add a using 1; rw [one_smul]
lemma dY_curve (hp:Differentiable ℝ F)(x:ℝ): dY F x=fderiv ℝ F (x,0) ξ := by
    obtain h:= ( direction ξ hp (x,0) 0 ).deriv; simp_rw [zero_smul,add_zero, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,mul_zero,mul_one, zero_add, add_zero] at h; exact h
lemma φ (Q:L) {v:ℝ→ L→L[ℝ] E}{V:L→L[ℝ] E}(t:ℝ)(hp:HasDerivAt v V t): HasDerivAt (fun x=> v x Q) (V Q) t:= by
    exact ( (ContinuousLinearMap.apply ℝ E Q).hasFDerivAt.comp_hasDerivAt t hp )
lemma dY_s (hp:ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dY F):= by
    rw [ funext (dY_curve (hp.differentiable (by simp))) ]
    refine ((( ContinuousLinearMap.apply ℝ E ξ ).contDiff.comp ( hp.fderiv_right (by simp) )).comp ( f:= fun x:ℝ=>(x,(0:ℝ))) ( contDiff_id.prodMk contDiff_const ))
lemma tooth_dir (hp:ContDiff ℝ ∞ F): tooth F=fderiv ℝ (fderiv ℝ F) 0 ν ξ := by
    rw [tooth,funext (dY_curve (hp.differentiable (by simp))) ]
    obtain h:= (φ ξ 0 (direction ν (( hp.fderiv_right (m:=∞) (by simp) ).differentiable (by simp)) (ofXY 0 0) (0:ℝ)) ).deriv; -- adjust
    rw [zero_smul,add_zero,show ofXY 0 0=(0:ℝ×ℝ) from rfl] at h; simpa only [zero_smul,add_zero,zero_add,mul_one,Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero]  using h
lemma charged (x:Y)(hp:ContDiff ℝ ∞ F): ray_read F x = ((1/2):ℝ) • fderiv ℝ (fderiv ℝ F) 0 x x := by
    unfold ray_read; congr 1
    have hx(t:ℝ) : HasDerivAt (fun t:ℝ=>F (t • x)) ( fderiv ℝ F (t • x) x ) t:= by simpa only [zero_add] using direction x (hp.differentiable (by simp)) 0 t
    rw [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, funext (fun x=>(hx x).deriv) ]
    simpa only [ zero_smul,zero_add ] using ( φ x 0 ( direction x ((hp.fderiv_right (m:=∞) (by simp)).differentiable (by simp)) 0 0 ) ).deriv
def mixed (F:Y→E):= (1/2:ℝ) • (ray_read F (ν+ξ)-ray_read F (ν-ξ))
lemma read_mixed (hp:ContDiff ℝ ∞ F): mixed F=tooth F:= by
    rw [mixed,charged _ hp,charged _ hp,tooth_dir hp]; have he:= hp.contDiffAt.isSymmSndFDerivAt (x:=0) (n:=∞) (by simp; exact WithTop.coe_le_coe.mpr ( (le_top : (2:ℕ∞) ≤ ⊤) ));
    simp_rw [map_add,map_sub,ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, he ν ξ]; module
lemma swap (hp:ContDiff ℝ ∞ F): tooth (F ∘ Prod.swap)=tooth F:= by
    have ht:ContDiff ℝ ∞ (F ∘ Prod.swap):= hp.comp (contDiff_snd.prodMk contDiff_fst)
    rw [← read_mixed ht, ← read_mixed hp]; unfold mixed
    suffices ∀ p:Y,ray_read (F ∘ Prod.swap) p=ray_read F p.swap by
      have he : (ν+ξ).swap=ν+ξ:= by ext <;> norm_num [ofXY]
      have hu : (ν-ξ).swap=-(ν-ξ):= by ext <;> norm_num [ofXY]
      rw [this,this,hu,he]; repeat rw [charged _ hp]
      simp only [map_neg,ContinuousLinearMap.neg_apply,neg_neg]
    intro p; unfold ray_read; congr

-- a direct test-build lemma, allowing pricing by ∑∂y at fixed x and then t derivative
lemma sum_tooth {I:Type}(s:Finset I){f:I→Y→E}(hp:∀ i∈s, ContDiff ℝ ∞ (f i)):
    tooth (fun x=>∑ i∈s,f i x)=∑ i∈s,tooth (f i):= by
    have ht(x:ℝ):dY (fun x=>∑ i∈s,f i x) x=∑ i∈s,dY (f i) x := deriv_fun_sum (fun i hi=> (( hp i hi |>.comp (f:=fun t:ℝ=>(x,t)) (contDiff_const.prodMk contDiff_id) ).differentiable (by simp) 0 ) )
    rw [tooth, funext ht, deriv_fun_sum ]; · rfl
    exact fun i hi=> ( dY_s (hp i hi) ).differentiable (by simp) 0
lemma tooth_add (hp:ContDiff ℝ ∞ F)(ht:ContDiff ℝ ∞ H): tooth (fun x=>F x+H x)=tooth F+tooth H:= by
    let K(x:Bool)(t:Y):= if x then F t else H t
    obtain hh:= sum_tooth ( f:=K ) Finset.univ (by intro i _; cases i; exacts [ht,hp])
    simp [K] at hh; exact hh
lemma tooth_linear (hp:ContDiff ℝ ∞ F)(L:E→L[ℝ] L): tooth (L ∘ F) = L (tooth F):= by
    have he(x:ℝ): dY (L∘F) x=L ( dY F x ):= (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) ( ( ( hp.comp (contDiff_const.prodMk contDiff_id) ).differentiable (by simp) _).hasDerivAt)).deriv
    rw [tooth, funext he]; exact ( L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (( dY_s hp ).differentiable (by simp) 0|>.hasDerivAt) ).deriv

end mixed
end
end YM.SignedWilsonExpansion.Heter
