import YM.OPE.Compatible.Harks.Velt
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
abbrev Mints {s:ℕ}(E:Fin s→Type):= (∀ i:Fin s,E i)
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
def trims (i:ℕ)(c:S!):Prop:=∀ j: Fin s,j.val< i→ c j=0
def Edgewise (P:L!):Prop:=∀ (i:ℕ)(v:S!), trims i v→ trims i (P v)
noncomputable def stride (P:L!)(i:Fin s): E i→L[ℝ] E i:= proj i ∘L P ∘L ContinuousLinearMap.single (R:=ℝ) E i -- parentheses
structure Assist (T:∀ i: Fin s,Cuts d μ v b (E i) G)(R:L!):Prop where
   arum : Edgewise R
   gait (i:Fin s): Grooved (T i) (stride R i)
section
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}{z z':∀ j:Fin s,E j}
-- trims sub
omit [∀ i,NormedSpace ℝ (E i)] in
lemma trims.plus (h:trims k z)(hp:trims k z'): trims k (z+z'):= fun i hi=> by rw [Pi.add_apply,h i hi,hp i hi,add_zero]
omit [∀ i,NormedSpace ℝ (E i)] in
lemma trims.sub (h:trims k z)(hp:trims k z'): trims k (z-z'):= fun i hi=> by rw [Pi.sub_apply,h i hi,hp i hi, sub_self]
lemma trims.unit (h:trims k z)(a:ℝ): trims k (a • z):= fun i hi=> by rw [Pi.smul_apply,h i hi,smul_zero]
omit [∀ i,NormedSpace ℝ (E i)] in
lemma trims.be (z:S!):trims 0 z:=fun _ h=>by omega
section
omit [∀ i,NormedSpace ℝ (E i)]
lemma trims.up (i:Fin s)(h:trims i.val z)(hp:z i=0): trims (i.val+1) z:=by
    intro j hj; by_cases ht:j=i; subst j; exact hp; apply h _; have he:j.val≠i.val:= Fin.val_injective.ne ht; omega
lemma trims.drop (h:trims k z)(hx:j≤ k):trims j z:=fun i hi=> h i (lt_of_lt_of_le hi hx)
lemma trims.limb (h:trims s z): z=0:=funext fun i=> h i i.isLt
lemma nt(i:Fin s)(w:E i): trims i.val (Pi.single i w):=by intro j hj; exact Pi.single_eq_of_ne (Fin.ne_of_val_ne (by omega)) _
end
lemma scissor (hp:Edgewise p) (i:Fin s)(z:S!)(h:trims i.val z): p z i=stride p i (z i):=by
     let x:S!:=Pi.single i (z i); have hx: x i=z i:=Pi.single_eq_same ..; have ht:= trims.up i (h.sub (nt i (z i))) (by rw [Pi.sub_apply,Pi.single_eq_same,sub_self]); have hh : trims (i.val+1) (p z-p x):=map_sub p z x ▸ hp (i.val+1) _ ht; exact sub_eq_zero.mp (hh i (by omega)) -- field of-index
lemma combe (hp:Edgewise p): Edgewise (Ux p r):=by intro i z hz; rw [shiftUx]; exact trims.sub (hp _ z hz) (hz.unit _)
lemma followPow (hp:Edgewise p)(i:ℕ):Edgewise (p^i):=by induction i with | zero=> simp only [pow_zero]; exact fun i _ ht=>ht| succ i ih=> rw [pow_succ']; intro j z h; rw [byway]; exact hp _ _ (ih _ _ h)
lemma snow (hp:Edgewise p) (i:Fin s)(j:ℕ)(h: trims i.val z): (p^j) z i=(stride p i ^ j) (z i):=by
     induction j with
     | zero=> simp
     | succ j ih=> rw [pow_succ',pow_succ',byway,byway,scissor hp i _ (followPow hp j _ _ h),ih]
lemma byjack (p:L!)(i:Fin s)(r:ℝ): stride (Ux p r) i=Ux (stride p i) r:=by
     ext j; rw [shiftUx]; change Ux p r (Pi.single i j) i= _ ; rw [shiftUx,Pi.sub_apply, Pi.smul_apply,Pi.single_eq_same];rfl
end
end YM.OPE.Hark
