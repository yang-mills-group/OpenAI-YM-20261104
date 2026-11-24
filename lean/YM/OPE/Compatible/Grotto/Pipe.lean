import YM.OPE.Compatible.Grotto.Apron
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
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Finset Drift
variable {H:Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
def fore (z:S!)(i:ℕ):S!:=fun j=> if j.val< i then z j else 0
omit [∀ i,NormedSpace ℝ (E i)] in
lemma foreW(i:ℕ)(z:S!): ∑ j ∈ (univ.filter fun j:Fin s=> j.val< i), Pi.single j (z j) = fore z i:=by
    funext j;rw [Finset.sum_apply]; by_cases ht:j.val< i
    · rw [Finset.sum_eq_single j]; rw [Pi.single_eq_same];exact (if_pos ht).symm; intros b _ hn; exact Pi.single_eq_of_ne hn.symm _; exact fun h=>False.elim (h (Finset.mem_filter.mpr ⟨mem_univ _,ht⟩))
    rw [Finset.sum_eq_zero]; exact (if_neg ht).symm; intro k hk; exact Pi.single_eq_of_ne (Fin.ne_of_val_ne (by have he:=(mem_filter.mp hk).2;omega)) _
omit [∀ i,NormedSpace ℝ (E i)] in
lemma early (z:S!)(i:ℕ): trims i (z-fore z i):=by intro j hj; rw [Pi.sub_apply]; unfold fore; rw [if_pos hj,sub_self]
def TameK (i:ℕ)(r:ℝ)(a w:H→ℝ)(f:H→ℕ→ Mints E):Prop:=∀ j: Fin s,j.val< i→TameP r a w (fun x n=> f x n j)
lemma pointK (p: TameP r a w f)(i:ℕ) :TameK i r a w f:=fun j _=> TameP.cast (proj j) p
lemma TameK.take (p:TameK i r a w f)(ha:1 ≤ a)(hw:0 ≤ w): TameP r a w (fun i' n=>fore (f i' n) i):=by
    let P(j:Fin s)(x:H)(n:ℕ):Mints E:=Pi.single j (f x n j); let t:=univ.filter fun j:Fin s=>j.val< i; have ht(j:Fin s)(hx:j∈ t): TameP r a w (P j):= TameP.cast (ContinuousLinearMap.single (R:=ℝ) E j) (p j ((mem_filter.mp hx).2)); have H:= TameP.set t P ha hw ht; convert! H using 1; apply funext; intro x; funext n; rw [Finset.sum_apply,Finset.sum_apply]; exact (foreW i (f x n)).symm
-- ∀ TameAll
lemma TameK.all (p:TameK s r a w f)(ha:1 ≤ a)(hw:0 ≤ w): TameP r a w f:=by
     have ht:= TameK.take p ha hw; convert! ht using 1; funext i n j; exact (if_pos j.isLt).symm
lemma peb (T:S!→L[ℝ] S!)(v:S!)(i:Fin s)(hp:Edgewise T): T v i=stride T i (v i)+ T (fore v i.val) i:=by
    let y:= fore v i.val; have hx:T v i=T (v-y) i+ T y i:=by rw [map_sub,Pi.sub_apply,sub_add_cancel]
    rw [hx, scissor hp _ _ (early v i.val)]; rw [Pi.sub_apply,show fore v i.val i=0 from if_neg (by omega),sub_zero]
end YM.OPE.Hark
