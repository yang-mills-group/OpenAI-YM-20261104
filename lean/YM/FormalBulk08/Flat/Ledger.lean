import YM.FormalBulk08.Flat.Reserve

/-!
Packing fine-end warm operands with cost in `Laurent.Width`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary
open scoped Topology BigOperators Matrix
variable {G : Gauge} {L c f : Side} {S : StepData c f} {η A : ℝ} {j t : ℕ}

-- open Classical locally; some all-type matrix lemmas use explicitly supplied computable instances.
section block
variable (α β : Type) [Fintype β] [DecidableEq β]

def onBlocks (L : Side) (X : Row α β) : Row (Co L α) (Co L β) := fineCompose X (unitRow (Co L β))

lemma onBlocks_pay {X : Row α β} (he : 0 ≤ η) (h : X.strip η A) (L : Side) :
    (onBlocks α β L X).strip η ((Fintype.card β:ℝ)*A) := by
  simpa only [onBlocks,mul_one] using (strip_fine he h (strip_unit (α:=Co L β)))
lemma onBlocks_service (L : Ratio c f) {X : Row α β} (he : 0 ≤ η) (h : X.strip η A) :
    (onBlocks α β L.count X).acts c = Matrix.submatrix (X.acts f) (splitCo L α).symm (splitCo L β).symm := by
  have hx : installed L (onBlocks α β L.count X)=X.acts f * installed L (unitRow (Co L.count β)) := installed_fine L he h strip_unit
  ext i j
  let s:= (splitCo L α)
  let b:= (splitCo L β)
  obtain ⟨y,rfl⟩ := s.surjective i
  obtain ⟨x,rfl⟩ := b.surjective j
  rw [Matrix.submatrix_apply, s.symm_apply_apply,b.symm_apply_apply]
  have he := congr_fun (congr_fun hx y) (b x)
  unfold installed at he; rw [Matrix.submatrix_apply,id_eq,Matrix.mul_apply, acts_unit] at he
  apply he.trans; rw [Finset.sum_eq_single x]; swap
  · intro a _ ha; simp [b,ha]
  swap; · simp
  simp [Matrix.one_apply,b]
end block

def shadedRows (G : Gauge) (R : Row (TypeFace j) (TypeFace t)) : Row (Loc G j) (Loc G t) :=
    fun x y z=> if x.2=y.2 then R x.1 y.1 z else 0
lemma shades_pay (X : Row (TypeFace j) (TypeFace t)) (hA : 0 ≤ A) (h : X.strip η A) :
    (shadedRows G X).strip η A := by
  intro i j; unfold shadedRows; split_ifs with hx; exact h _ _; simp [Laurent.Width,SumBudget,hA]
lemma shades_reads (G : Gauge) (X : Row (TypeFace j) (TypeFace t)) (p : Momentum) :
    (shadedRows G X).read p=tintedLocal G (X.read p) := by
  ext i j; unfold tintedLocal Row.read; by_cases h : i.2=j.2 <;> simp [shadedRows,h,Laurent.read]
lemma shades_acts (c : Side) {X : Row (TypeFace j) (TypeFace t)} (hs : X.safe) :
    (shadedRows G X).acts c=patron G (X.acts c) := by
  apply prom_inj
  apply arcs_lock c (Jaunt.row (shadedRows G X) ?_) (palette_ship _ hs) (fun p=> shades_reads ..)
  intro i j; unfold shadedRows; split_ifs with h; exact hs _ _; simp

def cutRow (G : Gauge) (L : Side) : Row (Co L (Loc G 1)) (ParcelG G L) :=
    fun i j=>Sum.elim (fun a => unitRow (Co L (Loc G 1)) i a) (fun _=>0) j
lemma cut_pay (G : Gauge) (L : Side) (η : ℝ) : (cutRow G L).strip η 1 := by
  intro i j; rcases j with j|j; exact strip_unit _ _
  simp [cutRow,Laurent.Width,SumBudget]
lemma cut_delivery (S : StepData c f) : (cutRow G S.patch.L).acts c=repackM (unitSplit G S 1) (clothe G S) (butt G c f) := by
  classical
  apply prom_inj
  have hh:= (Whole.safe (A:=cutRow G S.patch.L) ⟨1,1,one_pos,cut_pay _ _ _⟩)
  refine arcs_lock c (Jaunt.row _ hh) (butt_travel (G:=G) (S:=S)) (fun p=>?_)
  ext i (l|l)
  · rw [show Row.read (cutRow G S.patch.L) _ i (.inl l)=_ from (rfl : _ = (unitRow _).read (mon p) i l),read_unit]; simp [shardX,Pi.single_apply,Matrix.one_apply]
  simp [Row.read, cutRow,Laurent.read,shardX]

/-- Charge a difference metric on a fine level, tagged by its adjacent patch;
post-block budget spent linearly in the size of the metric error. -/
def embossed (G : Gauge) (P : Patch) (R : Row (TypeFace 2) (TypeFace 2)) :=
  let X:=cobound 1
  let T:=cutRow G P.L
  let U:=onBlocks _ _ P.L (shadedRows G (composeRows (composeRows (transRows X) R) X))
  composeRows (composeRows (transRows T) U) T
lemma embossed_bill (G : Gauge) (P : Patch) (η : ℝ) (hη : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ (R : Row (TypeFace 2) (TypeFace 2)) (A : ℝ),0≤A → R.strip η A →
      (embossed G P R).strip η (C*A) ∧ ∀ c : Side, ∀ K : KernelChoices,
        let S:=primary P K c; let T:=clothe G S; let U:=butt G c (c*P.L)
        (embossed G P R).acts c=repackM T T (Uᵀ*patron G (Precision.K (R.acts (c*P.L)))*U) := by
  let m : ℝ:=Fintype.card (Co P.L (Loc G 1)); let n : ℝ:= Fintype.card (Loc G 1); let j : ℝ:= Fintype.card (TypeFace 2)
  obtain ⟨E,hE,H⟩:=delta_budget 1 η
  let B:=m*m*n*j*E*j*E
  have hb : 0 ≤ B := by unfold B m n j; positivity
  refine ⟨max 1 B,lt_max_of_lt_left one_pos,fun R A hA h=> ?_⟩
  let D:= cobound 1; let U:=composeRows (transRows D) R; let X:=composeRows U D
  let Y:= shadedRows G X; let Z:= onBlocks _ _ P.L Y; let T:=cutRow G P.L
  have hD : D.strip η E:=H
  have hU : U.strip η (j*(E*A)):= strip_compose hη.le (strip_trans H) h
  have hX : X.strip η (j*(j*(E*A)*E)):=strip_compose hη.le hU hD
  have hY := shades_pay (G:=G) X (by unfold j; positivity) hX
  have hZ : Z.strip η (n*(j*(j*(E*A)*E))):=onBlocks_pay _ _ hη.le hY _
  have hT : T.strip η 1:= cut_pay _ _ _
  have hk := strip_compose hη.le (strip_trans hT) hZ
  constructor
  · apply strip_mono (strip_compose hη.le hk hT) le_rfl
    change m * (m*(1*(n*_))*1) ≤ _
    calc
      _ = B * A := by unfold B; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hA
  intro c K S t V
  classical
  have he : (Z.acts c)=repackM (unitSplit G S 1) (unitSplit G S 1) (patron G (Precision.K (R.acts (c*P.L)))) := by
    rw [show Z.acts c= _ from onBlocks_service (L:=S.ratio) _ _ hη.le hY]
    rw [show Y.acts (c*P.L)=_ from shades_acts (G:=G) _ (X.rights _ _ hX hη.le), acts_compose hη.le hU hD,acts_compose hη.le (strip_trans H) h, acts_trans]
    rfl
  calc
    _ = ((T.acts c)ᵀ * Z.acts c)*(T.acts c) := by rw [← acts_trans,← acts_compose hη.le (strip_trans hT) hZ,← acts_compose hη.le hk hT]; rfl
    _ = _ := by rw [show T.acts c= _ from (cut_delivery S (G:=G)),he,repack_multiply _ (unitSplit G S 1),repack_multiply _ (unitSplit G S 1),repack_rotate]; rfl

lemma patron_minus {R Q : Matrix (Body 1 f) (Body 1 f) ℝ} :
    patron G (R-Q) = patron G R-patron G Q := by
  apply Stationary.testers; intro x y
  rw [Matrix.sub_mulVec,patron_fee,patron_fee,patron_fee]
  apply congr_arg _; ext1 k; unfold uniformM; dsimp; rw [Matrix.sub_mulVec]; rfl

lemma parcel_difference {P : Patch} {K : KernelChoices} (U V : Train j) (c : Side) (t : (primary P K c).Choices)
    (R : Row (TypeFace 2) (TypeFace 2))
    (h : R.acts (c*P.L) = (pink K.penalty V).acts (c*P.L)-(pink K.penalty U).acts (c*P.L)) :
    let T:= clothe G (primary P K c); let Y:= butt G c (c*P.L)
    device P K c t V-device P K c t U=repackM T T (Yᵀ*patron G (Precision.K (R.acts (c*P.L)))*Y) := by
  intro T Y
  rw [h,Precision.K,Matrix.mul_sub,Matrix.sub_mul, patron_minus,Matrix.mul_sub,Matrix.sub_mul]
  dsimp only [device,meat,primary]
  ext a b
  simp only [Matrix.sub_apply,Matrix.add_apply,repackM,Matrix.submatrix_apply,Precision.K]; abel

lemma center_difference (G : Gauge) (P : Patch) (σ D : ℝ) (hσ : 0<σ) :
    ∃ C : ℝ,0<C ∧ ∀ (j : ℕ) (U V : Train j) (K : KernelChoices) (X Y : Row (ParcelG G P.L) (ParcelG G P.L)) (A : ℝ),
      Clerk G P K U X → Clerk G P K V Y → X.strip σ D → Y.strip σ D → Whole (pink K.penalty U) → Whole (pink K.penalty V) →
      0≤A → (minusRows (pink K.penalty U) (pink K.penalty V)).strip σ A →
      (minusRows X Y).strip σ (C*A) := by
  let n:ℝ:=Fintype.card (ParcelG G P.L)
  obtain ⟨C,hC,H⟩:= embossed_bill G P σ hσ
  let Z:=n*n*(D*C*D)
  refine ⟨max 1 Z,lt_max_of_lt_left one_pos,fun j U V K X Y A hX hY hR hQ hU hV hA H₀=> ?_⟩
  classical
  -- Resolvent identity at every physical period.
  let M:=minusRows (pink K.penalty U) (pink K.penalty V)
  obtain ⟨hr,hF⟩:=H M A hA H₀
  let E:=embossed G P M
  let W:=composeRows (composeRows X E) Y
  have hw: W.strip σ (n*(n*(D*(C*A))*D)):=strip_compose hσ.le (strip_compose hσ.le hR hr) hQ
  have hh : minusRows X Y= scaleRows (-1) W:= by
    apply bank_injective
        (Row.rights _ _ (strip_minus hR hQ) hσ.le) (Row.rights _ _ (strip_scale hw _) hσ.le)
    intro c
    let t := Classical.choice (chooseable c (c*P.L) (primary P K c)); let X':=X.acts c; let Y':=Y.acts c
    let F:=device P K c t V (G:=G); let B:=device P K c t U (G:=G)
    have hE : E.acts c=B-F := (hF c K).trans (parcel_difference (G:=G) V U _ t M (Whole.less hU hV _)).symm
    rw [acts_minus hσ.le hR hQ,acts_scale]
    unfold W; rw [acts_compose hσ.le (strip_compose hσ.le hR hr) hQ, acts_compose hσ.le hR hr, hE, Matrix.mul_sub,Matrix.sub_mul, Matrix.mul_assoc X' F, show X'*B=1 from mul_eq_one_comm.mp (hX c t),show F*Y'=1 from hY c t, Matrix.mul_one, Matrix.one_mul]; rw [neg_one_smul]; change X' - Y' = _; abel
  rw [hh]; exact strip_mono (strip_scale hw _) le_rfl ((show ‖(-1:ℝ)‖*(n*(n*(D*(C*A))*D))=Z*A by unfold Z; rw [norm_neg,norm_one]; ring).trans_le (mul_le_mul_of_nonneg_right (le_max_right ..) hA))
end YM.FormalBulk08.Flat
