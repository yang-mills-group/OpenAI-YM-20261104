import YM.XSpace.Grades
/-!
# Lifting frames and restricting. Pull and infinitesimal actions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} {E:Type} [AddCommMonoid E] [Module ℂ E]
lemma may_change (T: FieldEnd G d): T∈Change G d ↔ T (leaf G d)=0 ∧ (∀ l≤d,∀ p:Sec G d,p.val∈shellSector G l→(T p).val∈shellSector G l) ∧ (∀ p,T (reel d p)=reel d (T p)) ∧ ∀ (s:Signed) p,T (ori s.ortho d p)=ori s.ortho d (T p):=Iff.rfl
private lemma rise_ok (T:Change G d) : step d ∘ₗ T.val ∘ₗ prev d∈ Change G (d+1):= by
  simp only [may_change,LinearMap.comp_apply]
  refine ⟨?_,?_,?_,?_⟩
  · rw [← show step d (leaf G d)=leaf G (d+1) from rfl,prev_step,T.property.1,map_zero]
  · intro l hl p h; by_cases he : l≤d
    · let P: Sec G d := ⟨p.val,chain he h⟩; rw [← show step d P=p from Subtype.ext rfl, prev_step]; exact T.property.2.1 _ he P h
    rw [show l=d+1 by omega]; exact Subtype.property _
  · intro p; rw [←prev_reel,T.property.2.2.1,reel_step]
  intro s p; rw [←prev_ori,T.property.2.2.2,ori_step]

def grow (d:ℕ): (Change G d)→ₗ[ℝ] Change G (d+1) where
  toFun T:=⟨_,rise_ok T⟩
  map_add' T U:= by apply Subtype.ext; ext1 p; change step d (T.val _ + U.val _)= step d _ + step d _; simp only [map_add,LinearMap.comp_apply]
  map_smul' a T:= by apply Subtype.ext; ext1 p; change step d (a • T.val _)= a • step d _; exact map_smul ((step d).restrictScalars ℝ) _ _
lemma grows (T:Change G d) (p:Sec G (d+1)): (grow d T).val p=step d (T.val (prev d p)):=rfl
lemma growth (T:Change G d) (p:Sec G d): (grow d T).val (step d p)=step d (T.val p):=by rw [grows,prev_step]

lemma dwindle (T:Change G (d+1)) (p:Sec G d): step d (prev d (T.val (step d p)))= T.val (step d p):=by
  let q: Sec G d:= ⟨_,T.property.2.1 d (Nat.le_succ _) (step d p) p.property⟩
  rw [← show step d q=T.val (step d p) from Subtype.ext rfl,prev_step]
private lemma fell_ok (T:Change G (d+1)): prev d ∘ₗ T.val ∘ₗ step d∈Change G d:=by
  simp only [may_change,LinearMap.comp_apply]; refine ⟨?_,?_,fun p=> ?_,fun s p=> ?_⟩
  · rw [show step d (leaf G d)=leaf G (d+1) from rfl,T.property.1,map_zero]
  · intro l hl p hp; change (step d (prev d _)).val∈ shellSector G l; rw [dwindle]; exact T.property.2.1 _ (le_trans hl (Nat.le_succ _)) _ hp
  · rw [reel_step,T.property.2.2.1,prev_reel]
  rw [ori_step,T.property.2.2.2,prev_ori]

def fell (d:ℕ): (Change G (d+1))→ₗ[ℝ] Change G d where
  toFun T:=⟨_,fell_ok T⟩
  map_add' T U:= by apply Subtype.ext; ext1 p; change prev d (T.val _ + U.val _)=prev d _ + prev d _; simp only [map_add,LinearMap.comp_apply]
  map_smul' a T:= by apply Subtype.ext; ext1 p; change prev d (a • T.val _)= a • prev d _; exact map_smul ((prev d).restrictScalars ℝ) _ _
lemma fell_apply (T:Change G (d+1)) (p:Sec G d): (fell d T).val p=prev d (T.val (step d p)):=rfl
lemma fells (T:Change G (d+1)) (p:Sec G d): step d ((fell d T).val p)=T.val (step d p):= dwindle ..
lemma renewed (T:Change G d): fell d (grow d T)=T:=by apply Subtype.ext; ext1 p; rw [fell_apply,growth,prev_step]

variable {l m j:ℕ}

def recruit (F : Sec G d→ₗ[ℂ] Sec G l): Correl G l E→ₗ[ℂ] Correl G d E where
  toFun P n:= {
    toFun t:= (P n t).compLinearMap fun _=> F
    map_add' a b:= by apply MultilinearMap.ext; intro p; rw [map_add]; rfl
    map_smul' c a:= by apply MultilinearMap.ext; intro p; rw [map_smul]; rfl }
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
lemma recruits (F : Sec G d→ₗ[ℂ] Sec G l) (P:Correl G l E) (t:Test n) (p:Fin n→Sec G d): recruit F P n t p=P n t (F ∘ p):=rfl
lemma recruits_comp (F : Sec G d→ₗ[ℂ] Sec G m) (K: Sec G m→ₗ[ℂ] Sec G l) (P:Correl G l E): recruit F (recruit K P)= recruit (K ∘ₗ F) P:= rfl
lemma enroll (F : Sec G d→ₗ[ℂ] Sec G l) (X : FieldEnd G d) (Y : FieldEnd G l) (P : Correl G l E)
    (he : ∀ p,F (X p)=Y (F p)): varies (recruit F P) X=recruit F (varies P Y):=by
  ext n t p; rw [variation,recruits,variation]; simp_rw [recruits]; refine Finset.sum_congr rfl (fun i _=>?_); apply congr_arg; ext1 j; by_cases h:j=i <;> simp [h,he]
lemma refill (h:j≤d) (G:Gauge) : recruit (up h) (reference G d)=reference G j:= rfl
lemma recruits_slope (T:Change G (d+1)): recruit (step d) (gradient G (d+1) T)= gradient G d (fell d T) := by
  change recruit (step d) (varies (reference G (d+1)) T.val)=varies (reference G d) (fell d T).val; rw [← refill (Nat.le_succ d) G, enroll _ _ _ _ (fun p=> fells T p)]
end YM.XSpace.Normalize
