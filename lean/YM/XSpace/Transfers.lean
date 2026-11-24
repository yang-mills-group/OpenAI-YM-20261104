import YM.XSpace.Hoarding
/-!
# Complex triangular announcement restores alphabet after engineering

Unit kept, scaling includes exact grade powers even for downward corrections. No divisions inside normative implicit map.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Structure1
open Filter Set Function Lattice Chart2 Mu Furlough Normalize Foundation JetGauge Outline Shade Future Hoops Maxwell Maxwell.Free Bracket
open scoped Topology BigOperators Classical
variable {G:Gauge} (W:Initialize G) {d n j:ℕ} (c:Shade.Cut)
def Tri (G:Gauge)(d:ℕ): Submodule ℂ (FieldEnd G d) where
 carrier := {T| T (leaf G d)=0 ∧ ∀ l≤d,∀ p: Sec G d,p.val∈shellSector G l→(T p).val∈shellSector G l}
 zero_mem' :=⟨rfl,fun _ _ _ _=> Submodule.zero_mem _⟩
 add_mem' := by rintro F T ⟨h,H⟩ ⟨g,G⟩; exact ⟨by rw [LinearMap.add_apply,h,g,zero_add],fun i hi p hp=> Submodule.add_mem _ (H i hi p hp) (G i hi p hp)⟩
 smul_mem' := by rintro v F ⟨h,H⟩; exact ⟨by rw [LinearMap.smul_apply,h,smul_zero],fun i hi p hp=> Submodule.smul_mem _ v (H i hi p hp)⟩
lemma tri_may (F:FieldEnd G d): F∈ Tri G d ↔ F (leaf G d)=0 ∧ ∀ l≤d,∀ p:Sec G d,p.val∈shellSector G l→(F p).val∈shellSector G l := Iff.rfl

def gates (a:ℂ)(d:ℕ): FieldEnd G d:= ∑ i: Fin (d+1), a^i.val • (en (Nat.lt_add_one_iff.mp i.isLt) ∘ₗ Normalize.part d i)
lemma gate_wt (p:HP G j)(h:j≤d)(a:ℂ): gates (G:=G) a d (en h p)= a^j • en h p:=by
  unfold gates; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]; let k:jobs d:=⟨j,Nat.lt_add_one_iff.mpr h⟩; rw [Finset.sum_eq_single k]; change a^j • en h _=_; rw [part_same]; intro i _ hi; rw [part_other p (fun h=> hi (Fin.ext h)),map_zero,smul_zero]; simp
lemma canal (x:Cover)(a:ℝ)(he:0<a)(p:Sec G j)(h:j≤d): μ0 W d a x (up h (gates a j p)) = freeze (Trace.volume x (screenplay W j p)):=by
  nth_rw 1 [← enfits p]; simp_rw [map_sum,gate_wt, map_smul, en_up, μ0, entry,base_ice0,snaps,map_smul, smul_smul]
  rw [Bracket.screen,map_sum,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; have hy: base a= ((a:ℂ))⁻¹:=rfl; rw [hy,← mul_pow,mul_inv_cancel₀ (by exact_mod_cast he.ne'), one_pow,one_smul]; rfl

def classFee (a:ℝ)(n:ℕ):=(base a)^n • ((gates (G:=G) (a:ℂ) n) ∘ₗ repair W c n a)
def ready (a:ℝ)(d:ℕ): FieldEnd G d:= ∑ k:jobs d, up (Nat.lt_add_one_iff.mp k.isLt) ∘ₗ classFee W c a k ∘ₗ Normalize.part d k
lemma ready_one (p:HP G j)(h:j≤d)(a:ℝ): ready W c a d (en h p)= up h (classFee W c a j p):=by unfold ready; rw [LinearMap.sum_apply]; let k:jobs d:=⟨j,Nat.lt_add_one_iff.mpr h⟩; rw [Finset.sum_eq_single k]; change up h (classFee _ c _ _ (Normalize.part d j _))=_; rw [part_same]; intro i _ hi; rw [LinearMap.comp_apply,LinearMap.comp_apply,part_other p (fun h=>hi (Fin.ext h)),map_zero,map_zero]; simp
lemma ready_in (a:ℝ)(d:ℕ): ready W c a d∈ Tri G d:=by
  rw [tri_may]; constructor
  · let L:= leaf G 0; have he : en (le_refl 0) (Normalize.part 0 0 L)=L:= by have hh:=enfits L; simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero, Fin.val_zero] at hh; exact hh
    rw [← show en (Nat.zero_le d) (Normalize.part 0 0 L)=leaf G d from Subtype.ext (show _ from congr_arg (fun p:Sec G 0=>p.val) he),ready_one,classFee,LinearMap.smul_apply,LinearMap.comp_apply,strictly W c a _ (show _ from congr_arg (fun p:Sec G 0=>p.val) he),map_zero,smul_zero,map_zero]
  intro i hi p hp; let q:Sec G i:= ⟨p.val,hp⟩; rw [← show up hi q=p from Subtype.ext rfl,← enfits q]; simp_rw [map_sum,en_up,ready_one]; rw [Submodule.coe_sum]; exact Submodule.sum_mem _ fun i _=> (chain (Nat.lt_add_one_iff.mp i.isLt)) ((classFee W c a i.val (Normalize.part _ i q)).property)

-- apply to points at any tuple
def tangentP (F B: FieldEnd G d)(P:Point G d n): Point G d n := ∑ i:Fin n, P.compLinearMap (update (fun _=> F) i B)
lemma drawn (F B: FieldEnd G d)(P: Point G d n)(u:Tags G d n): tangentP F B P u=∑ i:Fin n,P (update (F ∘ u) i (B (u i))):=by simp only [tangentP,sum_apply, MultilinearMap.compLinearMap_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; apply congr_arg; funext j; by_cases h:j=i <;> simp [h]
def lot (X: Point G d n): FieldEnd G d→ₗ[ℂ] Point G d n where
  toFun T:= tangentP 1 T X
  map_add' F T:= by ext1 p; simp only [drawn, add_apply,LinearMap.add_apply,MultilinearMap.map_update_add, Finset.sum_add_distrib]
  map_smul' c F:= by ext1 p; simp only [drawn,LinearMap.smul_apply, MultilinearMap.map_update_smul,RingHom.id_apply,Finset.smul_sum,smul_apply]
lemma lots (X: Point G d n)(T:FieldEnd G d)(p:Tags G d n): lot X T p=∑ i:Fin n,X (update p i (T (p i))):= drawn 1 T X p

def adequate (T: FieldEnd G d)(a:ℝ)(x:Fin n→Cover): Point G d n:= replied W a x d-lot (blossom0 W d a x) T

variable (x:Fin n→Cover)(a:ℝ)(he:0<a){j:Fin n→ℕ}(p:∀ i,HP G (j i))(h:∀ i,j i≤d)
include he in
theorem confidence : adequate W (ready W c a d) a x (shells j p h)= startup W p Finset.univ c a x:=by
  rw [adequate,sub_apply,raw1,startup, lots]; apply congr_arg
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [pointer]; unfold shells; rw [ready_one,classFee,LinearMap.smul_apply,LinearMap.comp_apply,map_smul, map_smul,canal W _ a he]; unfold μ0; simp_rw [entry,base_ice0]; unfold LText; rw [LinearMap.comp_apply,LinearMap.comp_apply]; simp only [map_smul,smul_mul_assoc]; rfl
end YM.XSpace.Structure1
