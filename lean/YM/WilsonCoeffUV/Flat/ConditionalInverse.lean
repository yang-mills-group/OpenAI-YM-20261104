import YM.WilsonCoeffUV.Flat.RootStencil
/-!
# Wilson full-period recipe for the covering conditional covariance

The comparison uses a translated forest at flat. Define and bound the unique
kernel, including weighted ℓ¹ differences in the true period-free Laurent norm.
All power costs on the slice itself may be post-L; the strip is not post-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Precision Stationary
open Next.Free Tree Work.F08 FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} {c f L : Side} {S : StepData c f} {P:Patch} {K:KernelChoices} {s C : ℝ}

/-- Σ relation at all tori where the orientations etc use the same canonical forest. -/
def WickLine (P:Patch) (G:Gauge) (K:KernelChoices) (H:FreeResolvent.FaceRow)
    (R:Row (Co P.L (PAC G 1)) (Co P.L (PAC G 1))) :=
    ∀ (c f : Side) (hc:f.val=c.val*P.L.val),
      let S : StepData c f := ⟨P,K,hc⟩
      R.acts c=repackM (unitSplit G S 1) (unitSplit G S 1) (FreeResolvent.covariance G S (repeatF S) H)

section transfer
-- Auxiliary Bed normalizations in freezing may differ from unmodified array H.
variable {H : FreeResolvent.FaceRow} {B : Bed} (t:S.Choices)
open scoped Classical in
lemma transported (R : Row (ParcelG G S.patch.L) (ParcelG G S.patch.L))
    (h : R.acts c*fill S G t B=1) (he : S.patch.Branches S.kernel G)
    (hp : Precision.K (B.metric.acts f) = Precision.K (H.acts f)) :
    IsUnit (treeMatrix G S (repeatF S) H).det ∧
    repackM (unitSplit G S 1) (unitSplit G S 1) (covariance G S (repeatF S) H) = (projector G S.patch).acts c*R.acts c*((projector G S.patch).acts c)ᵀ := by
  let Q := frontR G S B + (postroom (G:=G) S t (inch S.patch.L))ᵀ * postroom (G:=G) S t (inch S.patch.L)
  let T := repeatF S
  let X := clothe G S; let Y:=unitSplit G S 1
  let V := repackM X.symm X.symm (R.acts c)
  have hv : V*Q=1 := by
    rw [← repack_return X X Q, ← repack_multiply]
    erw [h]; apply repack_unit
  have hK : treeMatrix G S T B.metric=treeMatrix G S T H := by
    unfold treeMatrix fullMatrix baseMatrix; rw [hp]
  let W := restrictTree G T * V * (restrictTree G T)ᵀ
  have hm : W * treeMatrix G S T H=1 := hK ▸ projecting T t B he V hv
  refine ⟨?_,?_⟩
  · exact isUnit_det_of_left_inverse hm
  have hx : treeInverse G S T H 0=W := by
    unfold treeInverse resolve; rw [zero_smul,add_zero]; exact inv_eq_left_inv hm
  rw [projector_period, covariance,hx]
  let D := insertion (plant (G:=G) T)
  let Z := toTree G T
  have hy : D*W*FreeResolvent.reduce G S T=Z*V*Zᵀ := by
    unfold Z; rw [coordinate_elim,transpose_mul]; unfold W
    change D*_* Dᵀ=_; simp only [Matrix.mul_assoc]; rfl
  change repackM Y Y (D * W * FreeResolvent.reduce G S T)=_
  rw [hy,repack_multiply Y X,repack_multiply Y X, repack_rotate]
  congr 2; exact repack_return X.symm X.symm (R.acts c)

end transfer

open scoped Classical in
lemma simpleK (P:Patch) (G:Gauge) (B : Bed) (H : FreeResolvent.FaceRow) (hs : 0≤s)
    (K:KernelChoices) (A D : ℝ) (_hA : 0≤A) (_hD : 0≤D) (h:P.Branches K G)
    (hp : ∀ f, Precision.K (B.metric.acts f) = Precision.K (H.acts f))
    (hD' : (projector G P).strip s D)
    (R : Row (ParcelG G P.L) (ParcelG G P.L)) (hR:R.strip s A)
    (hT : ∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩
                                           ∀ t,R.acts c*fill S G t B=1) :
    (∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩
                                              IsUnit (treeMatrix G S (repeatF S) H).det) ∧
    let F := composeRows (composeRows (projector G P) R) (transRows (projector G P))
    F.strip s (Fintype.card (ParcelG G P.L) * (Fintype.card (ParcelG G P.L) * (D*A)*D)) ∧ WickLine P G K H F := by
  classical
  constructor
  · intro c f hc S; let t := Classical.arbitrary S.Choices
    exact (transported (S:=S) t R (hT c f hc t) h (hp _)).1
  intro F
  refine ⟨strip_compose hs (strip_compose hs hD' hR) (strip_trans hD'),?_⟩
  intro c f hc S; let t:=Classical.arbitrary S.Choices
  unfold F; rw [acts_compose hs (strip_compose hs hD' hR) (strip_trans hD') c, acts_compose hs hD' hR c, acts_trans]
  exact (transported (S:=S) t R (hT c f hc t) h (hp _)).2.symm

/-- Need no equality between this *formal* Gaussian choice and any actual masked fluctuation covariance. -/
theorem line_available (K : KernelChoices) (G : Gauge) (j : ℕ) (hj: 4 ≤ j) :
    ∃ σ:ℝ, 0<σ ∧ ∀ P : Patch,P.J=j → P.Branches K G → ∃ C:ℝ, 0<C ∧ ∀ v:Train j,
      let H := record (pulse K.penalty v)
      (∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩; IsUnit (treeMatrix G S (repeatF S) H).det) ∧
        ∃ R, R.strip σ C ∧ WickLine P G K H R := by
  let k := K.penalty
  obtain ⟨γ,s,a,D,hp,hs,ha,hD,H⟩ := bid_bed k 0 K.penalty_pos le_rfl hj
  let p : Clip := ⟨γ,γ/32,1,hp,by linarith,by linarith,one_pos⟩
  obtain ⟨w,η,hw,hW,hη,_,h⟩ := cold_supply G K j a D s hs ha hD.le
  refine ⟨η,hη,?_⟩
  intro P hP hK
  obtain ⟨C,hC,hR⟩ := h P hP hK
  obtain ⟨B,hB,hb⟩ := projector_price (P:=P) (G:=G) hη.le
  let E : ℝ := Fintype.card (ParcelG G P.L) * (Fintype.card (ParcelG G P.L) * (B*C)*B)
  refine ⟨max 1 E,lt_max_of_lt_left one_pos,?_⟩
  intro v U
  obtain ⟨M,hm,hQ,hF,-,-⟩ := H p le_rfl v
  obtain ⟨Z,hz,hT⟩ := hR p M D hF (fun i j=> (hQ.2.1 i j).mono ((mul_le_of_le_one_left hw.le (inch_le _)).trans hW) le_rfl)
  have hK' n : Precision.K (M.metric.acts n)=Precision.K (U.acts n) := by
    rw [hm.metric]; unfold Precision.K
    rw [Matrix.mul_assoc,show (amend _ _ _).acts n*d 1 n=_ from (obligations k 0 K.penalty_pos le_rfl hj v n).2.2.1,Matrix.mul_assoc]; rfl
  obtain ⟨hh,hx,hV⟩ := simpleK P G M U hη.le K C B hC.le hB hK hK' hb Z hz hT
  exact ⟨hh,_,fun i j=> (hx i j).mono le_rfl (le_max_right _ E),hV⟩

-- A unique tree line in the coefficient prescription. Do not infer it from
-- one torus alone (nor infer Width costs from sphere-to-period estimates).
abbrev TreeRow (G:Gauge) (P:Patch) := Row (Co P.L (PAC G 1)) (Co P.L (PAC G 1))
abbrev ShapeRow := FreeResolvent.FaceRow
lemma WickLine.unique {H:ShapeRow} {X Y:TreeRow G P} (h : WickLine P G K H X) (g: WickLine P G K H Y) (hx:X.safe) (hy:Y.safe) : X=Y :=
    bank_injective hx hy fun n=> (h n (n*P.L) rfl).trans (g n _ rfl).symm
open scoped Classical in
def gamma (G : Gauge) (P : Patch) (K : KernelChoices) (H:ShapeRow) : TreeRow G P :=
    if h : ∃ R : TreeRow G P, R.safe ∧ WickLine P G K H R then h.choose else 0
lemma gamma_eq {X:TreeRow G P} {H : ShapeRow} (h:WickLine P G K H X) (g:X.safe) : gamma G P K H=X := by
    unfold gamma; split_ifs with h'
    · exact h'.choose_spec.2.unique h h'.choose_spec.1 g
    exact False.elim (h' ⟨X,g,h⟩)

/-- Quantifiers of the canonical coefficient line. -/
theorem actually_gamma (K : KernelChoices) (G:Gauge) (j:ℕ) (hj:4≤j) :
    ∃ σ:ℝ, 0<σ ∧ ∀ P : Patch,P.J=j → P.Branches K G → ∃ C:ℝ, 0<C ∧ ∀ v:Train j,
      let H:=record (pulse K.penalty v)
      (∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩; IsUnit (treeMatrix G S (repeatF S) H).det) ∧
      (gamma G P K H).strip σ C ∧ WickLine P G K H (gamma G P K H) := by
  obtain ⟨σ,hσ,h⟩ := line_available K G j hj; refine ⟨σ,hσ,?_⟩
  intro P hP hp; obtain ⟨C,hC,H⟩ := h P hP hp; refine ⟨C,hC,?_⟩
  intro v H'; obtain ⟨hh,R,hR,hv⟩ := H v
  exact ⟨hh, gamma_eq hv (Row.rights _ _ hR hσ.le) |>.symm ▸ hR, gamma_eq hv (Row.rights _ _ hR hσ.le) |>.symm ▸ hv⟩

-- compressed resolvent identity remains valid even with zero padding
lemma padded_diff {B H:ShapeRow} (T : Forest S.ratio) (hB:IsUnit (treeMatrix G S T B).det) (hH:IsUnit (treeMatrix G S T H).det) :
    covariance G S T B-covariance G S T H=covariance G S T H*(tensor G (Precision.K (H.acts f)- Precision.K (B.acts f)))*covariance G S T B := by
  classical
  let U:=treeMatrix G S T B; let V:=treeMatrix G S T H; let J:=insertion (plant (G:=G) T)
  have he : U⁻¹ - V⁻¹=V⁻¹*(V-U)*U⁻¹ := by rw [mul_sub, nonsing_inv_mul V hH, sub_mul,one_mul,mul_assoc,mul_nonsing_inv U hB,mul_one]
  let W := tensor G (Precision.K (H.acts f)-Precision.K (B.acts f))
  have hh : Jᵀ*W*J=V-U := by
    rw [show W=fullMatrix G S H-fullMatrix G S B from ?_, insertion.compress,Matrix.submatrix_sub]; rfl
    unfold fullMatrix baseMatrix W; simp only [tensor_add, add_sub_add_right_eq_sub]; ext i j; simp [tensor]; split <;> simp
  unfold covariance treeInverse resolve; simp only [zero_smul,add_zero]; change J*U⁻¹*Jᵀ-J*V⁻¹*Jᵀ=(J*V⁻¹*Jᵀ)*W*(J*U⁻¹*Jᵀ)
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, he, ← hh]; simp only [Matrix.mul_assoc]

def linearPad (G:Gauge) (P:Patch) (H:ShapeRow) : TreeRow G P := colorRow G (reblock P.L (hBlock H))
def padCost (_P:Patch) (s M:ℝ) := (Fintype.card (TypeFace 1):ℝ)* kinPrice s M
lemma padNN (h:0 ≤ C) : 0 ≤ padCost P s C := mul_nonneg (by positivity) (kinPrice_nn _ _ h)
lemma pad_linear (t:ℝ) (C:ℝ) : padCost P s (C*t)=padCost P s C*t := by unfold padCost kinPrice; ring
lemma linearPad_paid (hs:0≤s) {H:ShapeRow} (hf:H.strip s C) (ha:0≤C) : (linearPad G P H).strip s (padCost P s C) :=
    coloration_paid (G:=G) (expandI _ _ _) (expandI _ _ _) _ (padNN ha) (reblock_price hs (hBlock_width hs hf))
lemma linearPad_period (hs:0≤s) {H:ShapeRow} (hf:H.strip s C) :
    (linearPad G S.patch H).acts c=repackM (unitSplit G S 1) (unitSplit G S 1) (tensor G (Precision.K (H.acts f))) := by
  rw [← hBlock_periods hs hf]; exact colored_backed _ _ (reblock_periods S.ratio hs (hBlock_width hs hf))

-- consume tail budgets in EXACT slanted widths
lemma resolvent_paid {X Y:TreeRow G P} {H B:ShapeRow} {D:ℝ}
    (hX:WickLine P G K H X) (hY:WickLine P G K B Y)
    (hH : ∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩; IsUnit (treeMatrix G S (repeatF S) H).det)
    (hB : ∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩; IsUnit (treeMatrix G S (repeatF S) B).det)
    (hs:0≤s) (h:0 ≤ C) (hx:X.strip s D) (hy:Y.strip s D)
    (he : (minusRows B H).strip s C) (hp : Whole B) (hr : Whole H) :
    (minusRows X Y).strip s ((Fintype.card (Co P.L (PAC G 1)):ℝ)*
        ((Fintype.card (Co P.L (PAC G 1)):ℝ) * (D * padCost P s C)*D)) := by
  classical
  let U := linearPad G P (minusRows B H)
  have hu : U.strip s (padCost P s C) := linearPad_paid hs he h
  let V := composeRows (composeRows Y U) X
  have ht : V.strip _ _ := strip_compose hs (strip_compose hs hy hu) hx
  have hS : V=minusRows X Y := by
    apply bank_injective (Row.rights _ _ ht hs) (Row.rights _ _ (strip_minus hx hy) hs)
    intro L; let S : StepData L (L*P.L) := ⟨P,K,rfl⟩
    have ha : U.acts L=_ := linearPad_period (G:=G) (S:=S) hs he
    unfold V
    rw [acts_compose hs (strip_compose hs hy hu) hx L, acts_compose hs hy hu L, Work.F08.acts_minus hs hx hy L,ha,hp.less hr]
    let M:= unitSplit G S 1
    rw [hX L (L*P.L) rfl, hY L (L*P.L) rfl]
    have hh : Precision.K (B.acts (L*P.L)-H.acts (L*P.L))=Precision.K (B.acts (L*P.L))-Precision.K (H.acts (L*P.L)) := by unfold Precision.K; rw [Matrix.mul_sub,Matrix.sub_mul]
    rw [hh]; change _=repackM M M (covariance G S _ H-covariance G S _ B)
    rw [padded_diff (repeatF S) (hH L (L*P.L) rfl) (hB L (L*P.L) rfl),repack_multiply M M,repack_multiply M M]; rfl
  exact hS ▸ ht

end YM.WilsonCoeffUV
