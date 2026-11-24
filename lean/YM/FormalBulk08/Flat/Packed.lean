import YM.FormalBulk08.Flat.Stature

/-!
Pre-block exponentially priced conditional TREE covariance. Unwrap actual
periods exactly. No comparisons of the sort claiming complex background
nonzero gap from just this flat certificate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {j t : ℕ}
namespace Lodge

/-- Keep equality to the finite precision in native coordinates. -/
def Ready (G : Gauge) (K : KernelChoices) (T : Lodge P) (V : Train j)
    (U : Row (selected G P T) (selected G P T)) := ∀ c : Side,
      let S:=primary P K c; let E := T.forest (S:=S); let B:=testPrecision G S E V
      B.PosDef ∧ B*Matrix.submatrix (U.acts c) (T.splitting (S:=S)) (T.splitting (S:=S))=1

lemma prunes {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (p : α≃β)
    {A : Matrix α α ℝ} {B : Matrix β β ℝ} (h : repackM p p A*B=1) : A* repackM p.symm p.symm B=1 := by
  apply ((Matrix.reindex p p).injective); change repackM p p (A*repackM p.symm p.symm B)=repackM p p 1
  rw [repack_multiply _ p,show repackM p p (repackM p.symm p.symm B)=B by ext; simp [repackM], h, repack_unit]

open scoped Classical

def power (K : KernelChoices) (T : Lodge P) (B : Row (ParcelG G P.L) (ParcelG G P.L)) :=
    let H:=closeRow G P K T
    composeRows (composeRows H B) (transRows H)

lemma whole_wallet (K : KernelChoices) (T : Lodge P) (B : Row (ParcelG G P.L) (ParcelG G P.L))
    (h : Whole B) : Whole (T.power K B) := by
  obtain ⟨A,_,hx,hA⟩:= T.close_staged G K _ (show 0<(1:ℝ) from one_pos)
  have he : Whole (closeRow G P K T):=⟨_,_,one_pos,hx⟩
  exact (he.prod h).prod he.flipped
lemma catalogue_power (K : KernelChoices) (G : Gauge) (T : Lodge P) (V : Train j) {B : Row (ParcelG G P.L) (ParcelG G P.L)}
    (hp : 4≤j) (hK : P.Branches K G) (hB : Whole B) (h : Clerk G P K V B) : Ready G K T V (T.power K B) := by
  obtain ⟨D,_,hT,H⟩:=T.close_staged G K 1 one_pos
  let R:= closeRow G P K T
  have he : Whole R:=⟨_,_,one_pos,hT⟩
  intro c S E M
  let F:=clothe G S; let t:= Classical.choice (chooseable _ _ (primary P K c)); let L:=hang G S E
  let X:=repackM F.symm F.symm (B.acts c)
  have ht : meat (G:=G) S t V*X=1:= by
    apply prunes (B:=(B.acts c)) F
    exact h c t
  have hx : (T.power K B).acts c=repackM (T.splitting (S:=S)) (T.splitting (S:=S)) (L*X*Lᵀ) := by
    calc
      _ = R.acts c * B.acts c * (R.acts c)ᵀ := by rw [← acts_trans,← Whole.acts he hB,← Whole.acts (he.prod hB) he.flipped]; rfl
      _ = _ := by
        let A := T.splitting (S:=S) (G:=G)
        have hY : R.acts c=repackM A F L:=H c
        have hX : B.acts c=repackM F F X := by ext; simp [repackM,X]
        rw [hY,hX, show (repackM A F L)ᵀ=repackM F A (Lᵀ) from rfl]; symm
        rw [repack_multiply _ F (T.splitting (S:=S)),repack_multiply _ F]
  constructor
  · exact definite S hK _ _ _ ht hp
  have hb : Matrix.submatrix ((T.power K B).acts c) (T.splitting (S:=S) (G:=G)) (T.splitting (S:=S) (G:=G)) = L*X*Lᵀ := by
    rw [hx]; ext; simp [repackM]
  rw [hb]; exact triangle_pin _ hK _ _ _ ht

lemma power_add (K : KernelChoices) (T : Lodge P) (B A : Row (ParcelG G P.L) (ParcelG G P.L))
    (hb : Whole B) (ha : Whole A) : minusRows (power K T B) (power K T A) = power K T (minusRows B A) := by
  have H:=whole_wallet K T B hb
  have h:=whole_wallet K T A ha
  apply bank_injective (H.minus h).safe (whole_wallet _ _ _ (hb.minus ha)).safe
  intro c
  rw [H.less h]
  obtain ⟨D,_,hT,hS⟩:=T.close_staged G K 1 one_pos
  let X:= closeRow G P K T; have ht : Whole X:=⟨_,_,one_pos,hT⟩
  unfold power
  rw [Whole.acts (ht.prod hb) ht.flipped, Whole.acts (ht.prod ha) ht.flipped, Whole.acts (ht.prod (hb.minus ha)) ht.flipped, ht.acts hb, ht.acts ha, ht.acts (hb.minus ha), hb.less ha]; rw [Matrix.mul_sub, Matrix.sub_mul]

lemma power_pay (K : KernelChoices) (T : Lodge P) (σ : ℝ) (hσ : 0<σ) (G : Gauge) :
    ∃ C>0,∀ (B : Row (ParcelG G P.L) (ParcelG G P.L)) (A : ℝ), 0≤A → B.strip σ A → (power K T B).strip σ (C*A) := by
  obtain ⟨E,hE,hT,H⟩:= T.close_staged G K _ hσ
  let m:ℝ:= Fintype.card (ParcelG G P.L)
  refine ⟨max 1 (m*m*(E*E)),lt_max_of_lt_left one_pos,fun B A hA hB=> ?_⟩
  apply strip_mono (strip_compose hσ.le (strip_compose hσ.le hT hB) (strip_trans hT)) le_rfl
  change m*(m*(E*A)*E) ≤ _
  exact (show m*(m*(E*A)*E)=m*m*(E*E)*A by ring).trans_le (mul_le_mul_of_nonneg_right (le_max_right ..) hA)
end Lodge
end YM.FormalBulk08.Flat
