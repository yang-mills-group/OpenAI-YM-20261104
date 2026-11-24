import YM.MS.Book.Flo
/-!
# Formal leg-by-leg wavefunction renormalization with electric/antifield pairing

Actual λ-dependence specified per series at born. Propagate through symbol tables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Cylinder Lab Convolve
open PowerSeries (coeff)
variable {A B I : Type} {p:Sector A} (V:A→Cn)

section nv
variable [Fintype I] (B:Bonded p I)(hv:∀ i,V (B.plain i)*V (B.dual i)=1)

lemma trips (F H:T (Raw A ℂ)) : link B.BV true p (retrace F) (retrace H)=retrace (pairW (tokenL B.BV true p) F H) := by
    change B.BV (product p (retrace F) (retrace H))-product p (B.BV (retrace F)) (retrace H) -product p (Koszul.sign p true (retrace F)) (B.BV (retrace H))=_
    simp_rw [product_r, lap_r,twistl,product_r, ← map_sub]; congr 1; funext n; change (B.BV (pairW (product p) F H n) -_ - _) =_; simp_rw [paired,promised,map_sum,← Finset.sum_sub_distrib]; rfl

lemma rv_prod (f g: Raw A Cn) : rent V (product p f g) = product p (rent V f) (rent V g):= by
    funext l; rw [rent,scattered,scattered];
    let X:=allocate p l (R:=Cn); let Y (a b :List A):= f a*g b; change (l.map V).prod * X Y=_; rw [show (l.map V).prod * X Y =_ from (X.map_smul _ Y).symm] -- simp mismatch
    refine scatter_congr p _ _ _ ?_; intro a b he; change (l.map V).prod * (f a*g b)=rent V f a*rent V g b; have ht: (a.map V).prod*(b.map V).prod=(l.map V).prod:=by simpa using ((split_perm he).map V).prod_eq
    rw [← ht,rent,rent]; ring

def spanOp (A:Type)(V:A→Cn): Op A Cn where
    toFun:= rent V
    map_add' _ _:=funext fun _=> mul_add ..
    map_smul' _ _:= funext fun _=> mul_left_comm ..
include hv
lemma basisLap (F:Raw A Cn): B.BV (rent V F)=rent V (B.BV F):= by
    let X:=spanOp A V; have he i (F:Raw A Cn): D i (X F)= V i • X (D i F):= by funext l; exact mul_assoc ..
    change B.BV (X F)= X _;
    simp_rw [Bonded.BV,loop,LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply,he,map_sum,map_smul,he]; congr! 1; simp_rw [smul_smul,mul_comm (V (B.dual _)) (V (B.plain _)), hv, mul_one]
lemma inBasis (f g:Raw A Cn): rent V (link B.BV true p f g)=link B.BV true p (rent V f) (rent V g) := by
    let X:= spanOp A V
    change X (_-_ - _)= _-_ - _; rw [map_sub,map_sub]; unfold X spanOp; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [← rv_prod, basisLap _ _ hv,rv_prod,rv_prod, basisLap _ _ hv,basisLap _ _ hv]; rw [show rent V (Koszul.sign p true f)=Koszul.sign p true (rent V f) from funext fun _=> mul_left_comm ..] -- orientation
end nv

def merit (V:A→Cn)(n:ℕ): Op A ℂ where
   toFun F l:= coeff n (l.map V).prod * F l
   map_add' _ _:= funext fun _=> mul_add ..
   map_smul' _ _:=funext fun _=> mul_left_comm ..
lemma offer (n:ℕ)(F:Raw A ℂ) l: merit V n F l= coeff n (l.map V).prod*F l:=rfl
def taxi (V:A→Cn): T (Raw A ℂ)→ₗ[ℂ] T (Raw A ℂ) where
    toFun F n:=∑ i∈antidiagonal n,merit V i.1 (F i.2)
    map_add' _ _:= by ext; simp only [map_add,Pi.add_apply,sum_add_distrib]
    map_smul' c _:= by ext; simp only [map_smul,Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,Finset.sum_apply]
lemma receipt (F:T (Raw A ℂ)): retrace (taxi V F)=rent V (retrace F):= by
   funext l; apply PowerSeries.ext; intro n; rw [rback,rent, PowerSeries.coeff_mul]; simp_rw [rback]; rw [show taxi V F n=∑ i∈antidiagonal n,merit V i.1 (F i.2) from rfl,Finset.sum_apply]; rfl
lemma meterz [Fintype I] (B:Bonded p I) (F:T (Raw A ℂ))(hv:∀ i,V (B.plain i)*V (B.dual i)=1): promote B.BV (taxi V F)=taxi V (promote B.BV F) := retrace.injective (by simp_rw [← lap_r, receipt,basisLap _ _ hv, lap_r]) -- maybe order no rewrite
lemma meterr [Fintype I] (B:Bonded p I)(F H:T (Raw A ℂ))(hv:∀ i,V (B.plain i)*V (B.dual i)=1): pairW (tokenL B.BV true p) (taxi V F) (taxi V H)=taxi V (pairW (tokenL B.BV true p) F H) := by apply retrace.injective; rw [← trips, receipt V F,receipt V H, receipt, ← inBasis V B hv, trips B]
lemma tokensT [Fintype I](B:Bonded p I)(F:T (Raw A ℂ))(hv:∀ i,V (B.plain i)*V (B.dual i)=1): tokM B (taxi V F)=taxi V (tokM B F):= by simp only [tokM,meterz _ _ _ hv,meterr _ _ _ _ hv,map_add,map_smul]
end YM.MS.Book.Program
