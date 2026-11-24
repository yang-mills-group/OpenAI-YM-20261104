import YM.FormalBulk08.Flat.Predictor

/-!
Keep gradient and analytic rows for the tree response. At repeated steps
only the color extension of A0 used with pre-L constants; gradient
replacement charged per strict arrow (charged even for unused gauge modes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {k : KernelChoices} {c f L : Side} {t j : ℕ}

def grown (G : Gauge) {q l : ℕ} (W : Cross L (TypeFace q) (TypeFace l)) : Cross L (Loc G q) (Loc G l) :=
    fun i j x=> if i.2.2 = j.2 then W (i.1,i.2.1) j.1 x else 0
lemma grown_budget (G : Gauge) {q l} (W : Cross L (TypeFace q) (TypeFace l)) {A η : ℝ} (ha : 0≤A) (h : W.strip η A) :
    (grown G W).strip η A := by intro i j; unfold grown; split_ifs with hp; exact h _ _; simp [Width,SumBudget,ha]
lemma grown_act {q l} {S : StepData c f} (W : Cross S.patch.L (TypeFace q) (TypeFace l)) :
    installed S.ratio (grown G W)=patron G (installed S.ratio W) := by
  classical
  apply mat_confirm; intro v; rw [patron_fee]
  funext ⟨x,r,b⟩
  change ∑ j : Lines G c l,(installed S.ratio (grown G W) (x,r,b) j)*v j =
    ∑ j : Body l c,(installed S.ratio W (x,r) j)* (atPaint v b j)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_eq_single b]; swap
  · intro j _ hj; unfold installed; rw [Matrix.submatrix_apply, split_co]
    simp [Row.acts,grown, Ne.symm hj]
  swap; · simp
  unfold installed; rw [Matrix.submatrix_apply,Matrix.submatrix_apply,split_co,split_co]
  simp only [Row.acts,Matrix.of_apply,grown,id_eq,↓reduceIte]; rfl
lemma advance_grown {q l} (W : Cross L (TypeFace q) (TypeFace l)) s :
    advanceC L (grown G W) s=grown G (advanceC L W s) := by
  induction s with
  | nil=>rfl
  | cons b v h=>
    rw [advanceC, advanceC, h]; funext i j x; by_cases hp : i.2.2=j.2 <;> simp [hp,grown,forwardC]
lemma less_grown {q l} (X Y : Cross L (TypeFace q) (TypeFace l)) :
    minusRows (grown G X) (grown G Y)= grown G (minusRows X Y) := by funext i j x; by_cases h:i.2.2=j.2 <;> simp [grown,minusRows,h]

namespace Lodge
open scoped Classical
variable (G) (K : KernelChoices) (T : Lodge P)
def startMap (W : Cross P.L (TypeFace 1) (TypeFace 1)) := composeRows (transRows (cutRow G P.L)) (grown G W)
def parkMap (W : Cross P.L (TypeFace 1) (TypeFace 1)) := composeRows (footRow G P K T) (startMap G W)
def primaryMean (W : Cross P.L (TypeFace 1) (TypeFace 1)) := composeRows (closeRow G P K T) (startMap G W)

lemma startPay (G : Gauge) (P : Patch) (η : ℝ) (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ W : Cross P.L (TypeFace 1) (TypeFace 1), ∀ A : ℝ,0≤A → W.strip η A →
      (startMap G (P:=P) W).strip η (C*A) ∧
      ∀ K c, let S:=primary P K c; (startMap G (P:=P) W).acts c=
        repackM (clothe G S) (Equiv.refl (Lines G c 1)) ((butt G c (c*P.L))ᵀ*patron G (installed S.ratio W)) := by
  let a := (Fintype.card (Co P.L (Loc G 1)):ℝ)
  refine ⟨max 1 a,lt_max_of_lt_left one_pos,fun W A hA hh=>?_⟩
  have hg:=grown_budget G W hA hh; have hx:=cut_pay G P.L η
  constructor
  · exact strip_mono (strip_compose hη.le (strip_trans hx) hg) le_rfl
      (show a*(1*A) ≤ max 1 a*A by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hA)
  intro K c S
  let U:= grown G W
  have H : U.acts c=repackM (unitSplit G S 1) (Equiv.refl (Lines G c 1)) (patron G (installed S.ratio W)) := by
    have ht:= grown_act (S:=S) W (G:=G)
    rw [← ht]; unfold repackM installed; ext i j
    dsimp only [Matrix.submatrix_apply]; rw [(unitSplit G S 1).apply_symm_apply]; rfl
  unfold startMap; rw [acts_compose hη.le (strip_trans hx) hg,acts_trans, show (cutRow G P.L).acts c = _ from cut_delivery (G:=G) S, show (grown G W).acts c=_ from H]
  exact (repack_multiply _ (unitSplit G S 1) (Equiv.refl (Lines G c 1)) ((butt G c (c*P.L))ᵀ) (patron G (installed S.ratio W))).symm

lemma bothPay (η : ℝ) (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ W : Cross P.L (TypeFace 1) (TypeFace 1), ∀ A : ℝ, 0≤A → W.strip η A →
      (primaryMean G K T W).strip η (C*A) ∧ (parkMap G K T W).strip η (C*A) ∧
      ∀ c : Side,
        let S:=primary P K c
        let F:= T.forest (S:=S)
        let B:= (primaryMean G K T W).acts c
        let M:= patron G (installed S.ratio W)
        let U:= repackM (Equiv.symm (unitSplit G S 0)) (Equiv.refl (Lines G c 1)) ((parkMap G K T W).acts c)
        B=repackM (T.splitting (S:=S)) (Equiv.refl (Lines G c 1)) (rawMean G S F (installed S.ratio W)) ∧
          (dropRoot G S F)ᵀ*rawMean G S F (installed S.ratio W)=M+patron G (d 0 (c*P.L))*U := by
  obtain ⟨C,hC,H⟩:=startPay G P η hη
  obtain ⟨B,hB,h,hb⟩:= T.close_staged G K η hη
  obtain ⟨D,hd,E⟩:= T.foot_staged G K _ hη
  let u:= (Fintype.card (ParcelG G P.L):ℝ)
  let M:= max (u*B*C) (u*D*C)
  refine ⟨max 1 M,lt_max_of_lt_left one_pos,fun W A hA hw=> ?_⟩
  obtain ⟨hx,hC⟩:=H W A hA hw
  have hm : M≤max 1 M:=le_max_right ..
  have hv (z:ℝ) (he:u*z*C≤M) : u*(z*(C*A))≤max 1 M*A := by rw [← mul_assoc,← mul_assoc]; exact mul_le_mul_of_nonneg_right (he.trans hm) hA
  refine ⟨strip_mono (strip_compose hη.le h hx) le_rfl (hv _ (le_max_left ..)),strip_mono (strip_compose hη.le hd hx) le_rfl (hv _ (le_max_right ..)),fun c=> ?_⟩
  intro S F b m U
  let R:= clothe G S; let Y:= unitSplit G S 0; let g:=T.splitting (G:=G) (S:=S); let V:= (butt G c (c*P.L))ᵀ*m
  have ht : U=lead G S F * V := by
    have he : (parkMap G K T W).acts c=repackM Y (Equiv.refl _) (lead G S F * V) := by
      rw [parkMap,acts_compose hη.le hd hx,E c, hC K c]; exact (repack_multiply Y R _ _ _).symm
    unfold U; rw [he]; ext i j; simp only [repackM,Matrix.submatrix_apply]; exact congr_arg (fun z=> (lead G S F * V) z j) (Y.symm_apply_apply i)
  constructor
  · unfold b primaryMean; rw [acts_compose hη.le h hx,hb c,hC K c]; exact (repack_multiply g R _ _ V).symm
  change _ᵀ*(hang G S F*V)=_
  rw [← Matrix.mul_assoc, inject_out,imprint, Matrix.add_mul,ht,Matrix.mul_assoc,show butt G c _ * V=m by unfold V; rw [← Matrix.mul_assoc,(reproduced (G:=G) ..).1,Matrix.one_mul]]
end Lodge
end YM.FormalBulk08.Flat
