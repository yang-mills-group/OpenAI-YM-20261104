import YM.XSpace.Aisles
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series of permitted formal frame changes

Indicated ALL higher positive coefficients, even potentially diverging
when changing scheme. Unit preservation (at all orders), filtration and
H, real structure. Formal inverse asserted as such not allowing nonlinear
terms in fields. Same field-only pure letters at each step; precompose.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory PowerSeries
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d:ℕ}
private lemma change_left (A: Change G d) (B: Change G d): A.val * B.val ∈ Change G d:= by
  rw [may_change]; simp only [Module.End.mul_apply]; exact ⟨by rw [B.property.1,map_zero],fun i hi p h=> A.property.2.1 _ hi _ (B.property.2.1 i hi p h),fun p=>by rw [B.property.2.2.1,A.property.2.2.1],fun s p=>by rw [B.property.2.2.2,A.property.2.2.2]⟩
private lemma stand_left (A: Change G d) {B} (hB:B∈Change G d): stand A * B∈Change G d:=by unfold stand; rw [add_mul,one_mul]; exact Submodule.add_mem _ hB (change_left A ⟨B,hB⟩)
private lemma stand_right (A: Change G d) {B} (hB:B∈Change G d): B * stand A∈Change G d:=by unfold stand; rw [mul_add,mul_one]; exact Submodule.add_mem _ hB (change_left ⟨B,hB⟩ A)
lemma stand_times (T U: Change G d): ∃ V:Change G d, stand T * stand U=stand V:=by
  let B:Change G d:=⟨stand T*U.val,stand_left _ U.property⟩
  exact ⟨T+B,show stand T*(1+U.val)=1+(T.val+B.val) by rw [mul_add,mul_one]; unfold stand B; rw [add_assoc];rfl⟩
private lemma stand_raises (A:Change G d) (l:ℕ) (h:l≤d): ∃ B: Sec G l→ₗ[ℂ] Sec G l, ∀ p: Sec G l, up h (B p) = stand A (up h p):= by
  let B:=LinearMap.codRestrict (shellSector G l) (coeS d ∘ₗ stand A ∘ₗ up h) (fun p=>?h)
  case h => exact Submodule.add_mem _ p.property (A.property.2.1 l h (up h p) p.property)
  exact ⟨B,fun p=>rfl⟩
private theorem stand_unit_inverse (U:(FieldEnd G d)ˣ) (A:Change G d) (h:stand A= U.val): ∃ V: Change G d,U.inv=stand V:=by
  let L:=U.inv-1
  have hl(p): stand A (U.inv p)=p:= by rw [h]; exact DFunLike.congr_fun U.val_inv p
  have hu(p): U.inv (stand A p)=p:= by rw [h]; exact DFunLike.congr_fun U.inv_val p
  have he:Injective (stand A):= LeftInverse.injective hu
  have hh:L ∈ Change G d:=by
    unfold L; rw [may_change]; simp only [LinearMap.sub_apply, Module.End.one_apply]; refine ⟨?_,?_,?_,?_⟩
    · rw [show U.inv (leaf G d)=_ from (he (Eq.trans (hl _) (solitary A).symm)),sub_self]
    · intro l hk p hP; obtain ⟨B,hB⟩:= stand_raises A l hk
      have hj:=Submodule.inclusion_injective (chain (G:=G) hk); have hin: Injective B:= fun p q hp=>hj (he ((hB _|>.symm).trans ((congr_arg _ hp).trans (hB _))))
      let q: Sec G l:=⟨p.val,hP⟩; obtain ⟨r,hr⟩:=(LinearMap.surjective_of_injective hin) q; rw [show U.inv p= up hk r from he ((hl _).trans ((hB _).symm.trans ((congr_arg _ hr).trans rfl)).symm)]
      exact Submodule.sub_mem _ r.property hP
    · intro p; rw [map_sub]; congr 1; apply he; rw [hl,←stood_reel,hl]
    intro s p; rw [map_sub]; congr 1; apply he; rw [hl,←stood_ori,hl]
  exact ⟨⟨L,hh⟩,show _=1+(U.inv-1) by abel⟩

abbrev Pick (G:Gauge) (d:ℕ):= ℕ→(Change G d)
abbrev Guard (G:Gauge) (d:ℕ):= PowerSeries (FieldEnd G d)
abbrev pulling (u:Pick G d) (n:ℕ): FieldEnd G d:= if n=0 then stand (u n) else (u n).val
def deck (A: Pick G d): Guard G d := PowerSeries.mk (pulling A)
lemma decked (A: Pick G d) (n:ℕ): coeff n (deck A)=pulling A n:= coeff_mk ..
lemma pos_decked (A: Pick G d) {n:ℕ} (h:n≠0): coeff n (deck A)=(A n).val:= (decked A n).trans (if_neg h)
lemma const_deck (A:Pick G d): constantCoeff (deck A)=stand (A 0):= by rw [← coeff_zero_eq_constantCoeff_apply,decked,pulling,if_pos rfl]
lemma deck0 (G:Gauge) (d:ℕ): deck (0:Pick G d)=1:=by
  refine PowerSeries.ext fun n=>?_; rw [decked,pulling, coeff_one]; split_ifs with h; · subst n; exact stand0 d
  rfl
lemma faithful : Injective (deck (G:=G) (d:=d)):=by
  intro x y h; funext i; apply Subtype.ext; by_cases hi:i=0
  · subst i; ext1 p; exact add_left_cancel (show p+_=p+_ from DFunLike.congr_fun ((const_deck x).symm.trans ((congr_arg constantCoeff h).trans (const_deck y))) p)
  exact (pos_decked x hi).symm.trans ((congr_arg (coeff i) h).trans (pos_decked y hi))

structure Formal (T:Guard G d): Prop where
  actions : ∃ U:Pick G d, T=deck U
  seed : IsUnit T

theorem formal_deck (u:Pick G d) (h:Bijective (stand (u 0))) : Formal (deck u):= ⟨⟨u,rfl⟩, (PowerSeries.isUnit_iff_constantCoeff (φ:=deck u) (R:=FieldEnd G d)).mpr (by rw [const_deck]; exact (Module.End.isUnit_iff _).mpr h)⟩
private theorem actions_test {T:Guard G d} (h:∃ u:Change G d,constantCoeff T= stand u) (hp:∀ j:ℕ,j ≠ 0 → (coeff j T)∈Change G d): ∃ U:Pick G d,T=deck U:=by
  refine ⟨(fun j=> if hh:j=0 then h.choose else ⟨coeff j T,hp j hh⟩),PowerSeries.ext fun j=>?_⟩
  rw [decked,pulling]; split_ifs with hh; · subst j; exact (coeff_zero_eq_constantCoeff_apply _).trans h.choose_spec
  rfl

variable {X Y:Guard G d}
theorem Formal.one (G:Gauge) (d:ℕ): Formal (1:Guard G d):=⟨⟨0,(deck0 G d).symm⟩,isUnit_one⟩
theorem Formal.product (h: Formal X) (H:Formal Y): Formal (X*Y):=by
  refine ⟨?_,h.seed.mul H.seed⟩; obtain ⟨u,rfl⟩:=h.actions; obtain ⟨v,rfl⟩:=H.actions; apply actions_test _ _
  · rw [map_mul,const_deck,const_deck]; exact stand_times ..
  intro i hi; rw [coeff_mul]; apply Submodule.sum_mem; rintro ⟨a,b⟩ hab; rw [Finset.mem_antidiagonal] at hab; by_cases hx:a=0
  · simp only at hab; have hs:b ≠ 0:=by omega
    subst a; simp only [coeff_zero_eq_constantCoeff_apply,const_deck]; exact stand_left _ ((pos_decked v hs).symm ▸ (v b).property)
  dsimp only; rw [pos_decked u hx]; by_cases ht:b=0
  · subst b; rw [coeff_zero_eq_constantCoeff_apply,const_deck]; exact stand_right _ (u a).property
  rw [pos_decked v ht]; exact change_left ..

theorem Formal.reverse (h:Formal X): Formal (PowerSeries.invOfUnit X (((PowerSeries.isUnit_iff_constantCoeff (R:=FieldEnd G d)).mp h.seed).unit)):=by
  obtain ⟨u,rfl⟩:=h.actions; let U:= (((PowerSeries.isUnit_iff_constantCoeff (R:=FieldEnd G d)).mp h.seed).unit); let V:=deck u; let B:= PowerSeries.invOfUnit V U
  have hh : constantCoeff V=U.val:= Eq.symm (IsUnit.unit_spec _); have H := stand_unit_inverse U (u 0) ((const_deck u).symm.trans hh); have hv: constantCoeff B= U.inv:= constantCoeff_invOfUnit V U
  refine ⟨actions_test (hv.symm ▸ H) ?_, (PowerSeries.isUnit_iff_constantCoeff (R:=FieldEnd G d)).mpr (hv.symm ▸ (U⁻¹).isUnit)⟩
  intro i hi; induction i using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_invOfUnit n (deck u) U,if_neg hi]; change (-U.inv : FieldEnd G d) * _∈ _; rw [show ∀ C: FieldEnd G d, (-U.inv) * C = -(U.inv*C) from fun C=> by ext1 p; rfl]; refine @Submodule.neg_mem ℝ (FieldEnd G d) _ _ _ (Change G d) _ ?_; rw [show U.inv=stand H.choose from H.choose_spec]
    apply stand_left; apply Submodule.sum_mem; rintro ⟨a,b⟩ hw; split_ifs with hq; swap; · exact Submodule.zero_mem _
    simp only at hq; dsimp only; rw [Finset.mem_antidiagonal] at hw; simp only at hw; rw [pos_decked u (show a≠0 by omega)]; by_cases hx:b=0
    · subst b; change (u a).val * coeff 0 B∈ _; rw [coeff_zero_eq_constantCoeff_apply,hv,H.choose_spec]; exact stand_right _ (u a).property
    exact change_left _ ⟨_,ih b hq hx⟩

theorem reversal_exists (h:Formal X): ∃ U:Guard G d,Formal U∧U*X=1∧ X*U=1:=⟨_, Formal.reverse h,invOfUnit_mul _ _ (Eq.symm (IsUnit.unit_spec _)),mul_invOfUnit _ _ (Eq.symm (IsUnit.unit_spec _))⟩
end YM.XSpace.Normalize
