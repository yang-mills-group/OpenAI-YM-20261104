import YM.MS.Book.Triang
import YM.MS.Book.Ell
/-!
# Bundles over formal ring

Weight-space convergence at each word n sufficient. No topological uses.
    Expand on all count supports, use ∆ finite P algebra extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Cylinder Lab Convolve
open PowerSeries (coeff)
variable {A B I : Type*}
def frameA (R : T (Raw A ℂ)): Raw A Cn:= fun w=> PowerSeries.mk fun n=> R n w

def retrace : T (Raw A ℂ)≃ₗ[ℂ] Raw A Cn where
   toFun:= frameA
   invFun R n w:= coeff n (R w)
   map_add' U V:= by ext l n; change coeff n (frameA _ l)=coeff n (_+_); rw [map_add]; simp only [frameA,PowerSeries.coeff_mk]; rfl
   map_smul' c F:= by ext l n; change coeff n (frameA _ l)=coeff n (c • _); rw [map_smul]; simp only [frameA,PowerSeries.coeff_mk]; rfl
   left_inv _:= funext fun n=> funext fun l=> PowerSeries.coeff_mk ..
   right_inv _:= funext fun l=> PowerSeries.ext fun _=> PowerSeries.coeff_mk ..
lemma rback (F:T (Raw A ℂ))(l:List A)(n:ℕ): coeff n (retrace F l)=F n l:= PowerSeries.coeff_mk n (fun k=> F k l)
lemma reletter (F:T (Raw A ℂ))(i:A): D i (retrace F)=retrace (promote (D i) F):= rfl
lemma repays (c:ℂ)(F:T (Raw A ℂ)): retrace (c • F)= PowerSeries.C c • retrace F := by
   funext l; apply PowerSeries.ext; intro n; change coeff n _=coeff n (PowerSeries.C c * _); rw [PowerSeries.coeff_C_mul, rback,rback]; rfl
lemma twistl {p:Sector A}(F:T (Raw A ℂ))(b:Bool): Koszul.sign p b (retrace F)= retrace (promote (Koszul.sign p b) F):= by
   funext l; apply PowerSeries.ext; intro n; rw [at_sign,rback,promised,at_sign]; unfold cross; split <;> simp [rback]
lemma product_r (p:Sector A)(F H: T (Raw A ℂ)): product p (retrace F) (retrace H) = retrace (pairW (product p) F H):= by
    funext l; induction l generalizing F H with
    | nil=> apply PowerSeries.ext; intro n; rw [rback,nil_product, PowerSeries.coeff_mul]; simp_rw [paired,Finset.sum_apply,rback,nil_product]
    | cons i l ih=>
        rw [D_eval i (product p _ _),D_eval i (retrace _), D_product,twistl]; simp_rw [reletter,Pi.add_apply,ih]; have he: promote (D i) (pairW (product p) F H)= pairW (product p) (promote (D i) F) H + pairW (product p) (promote (Koszul.sign p (p i)) F) (promote (D i) H):=by 
                                                                              funext n; simp_rw [promised,paired,map_sum,D_product,Finset.sum_add_distrib, Pi.add_apply,paired,promised]
        rw [he,map_add]; rfl
variable {p:Sector A} (V:A→Cn)
-- ∆
lemma lap_r [Fintype I](B:Bonded p I)(F:T (Raw A ℂ)): B.BV (retrace F)=retrace (promote B.BV F):= by
   have he i:B.fee i = PowerSeries.C (B.fee i:ℂ):= by unfold Bonded.fee; cases h:p (B.plain i) <;> simp
   have hv i j: diffPair i j (retrace F)=retrace (promote (diffPair i j) F):= rfl
   simp only [Bonded.BV,loop,LinearMap.sum_apply,LinearMap.smul_apply,hv,he]; simp_rw [← repays,← map_sum]; congr 1; ext n; simp_rw [Finset.sum_apply, Pi.smul_apply,promised,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply] -- linter
end YM.MS.Book.Program
