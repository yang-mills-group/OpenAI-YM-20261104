import YM.Integration.ConditionalAffineForcing

/-! The authentic ordinary raw affine Jacobian in all three physical row arms.
These are the surrounding factors of a changed ordinary covariance in the
rooted scalar square and forcing. Each includes both of its Schur estimates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarOrdinaryColumns
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open ConditionalAffineForcing
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (k : S.Choices) (q : Admit)

def directRow (s : Signed) (i : tile G f) : Rows.Receipt G S := ((s,.inl ((i.1,plaqEquiv.symm i.2.1),false)),i.2.2)
def predictorRow (s : Signed) (i : raw G c) : Rows.Receipt G S := ((s,.inr (i.1,axisEquiv.symm i.2.1)),i.2.2)

def projected {ι : Type} (z : ι→Rows.Receipt G S) (B : Vec G c 1) := (rawRows T k q B).submatrix z id

/-- Native curvature-response matrix with the original coarse-field and signed-group normalization. -/
theorem direct (s : Signed) (B : Vec G c 1) (i : tile G f) (j : raw G f) :
    rawRows T k q B (directRow (S:=S) s i) j = (slip*Real.sqrt T.high.direct)*response S s B i j := by
  change slip*(Real.sqrt T.high.direct*((response S s B *ᵥ Pi.single j 1)
    (i.1,plaquette (plaqEquiv.symm i.2.1),i.2.2))) = _
  simp only [←plaq_map,Equiv.apply_symm_apply,Matrix.mulVec_single_one,Matrix.col_apply]
  ring

/-- Native analytic block predictor with its true signed source orientation. -/
theorem predictor (s : Signed) (B : Vec G c 1) (i : raw G c) (j : raw G f) :
    rawRows T k q B (predictorRow (S:=S) s i) j = -(slip*Real.sqrt S.kernel.penalty)*duct S s k B i j := by
  change slip*(-(Real.sqrt S.kernel.penalty*((duct S s k B *ᵥ Pi.single j 1)
    (i.1,coord (axisEquiv.symm i.2.1),i.2.2)))) = _
  simp only [show coord (axisEquiv.symm i.2.1)=i.2.1 from axisEquiv.apply_symm_apply _,
    Matrix.mulVec_single_one,Matrix.col_apply]
  ring

/-- Direct-arm two-sided Schur fee for every retained or uncut physical path admission. -/
theorem direct_price (s : Signed) (hc : 1<c.val) (n : ℕ) {γ δ : ℝ} (hg : 0<γ) (hd : 0≤δ) (he : δ≤γ) :
    Bundle (ray G c) (marks G c δ) (native c) (named S s) (home S) (projected T k q (directRow (S:=S) s))
      0 n γ (|slip*Real.sqrt T.high.direct| * lowBudget G S.patch S.kernel γ n) := by
  apply ((price_D (G:=G) S s hc n hg hd he).scale (slip*Real.sqrt T.high.direct)).glue
  apply Eventually.of_forall
  intro B
  ext i j
  exact (direct T k q s B i j).symm

/-- The transported plaquette arm costs the true full admitted path sum at each fixed selection. -/
theorem transported_price (s : Signed) (hc : 1<c.val) (n : ℕ) {b a δ : ℝ}
    (hb : 0<b) (ha : 0≤a) (hW : Sheet T.up b a) (hd : 0≤δ) (he : δ≤tier b n) :
    Bundle (ray G c) (marks G c δ) (native c) (named S s) (home S)
      (projected T k q (ConditionalAffineRowDifference.row (S:=S) s)) 0 n (wider b n)
      (|slip| * phasePrice G S.patch S.kernel n a b) := by
  apply ((funding S hc s hb ha hW hd he q).scale slip).glue
  apply Eventually.of_forall
  intro B
  ext i j
  exact (ConditionalAffineRowDifference.physical T k s q B i j).symm

/-- The true ordinary nonlinear predictor purchases both anchor orientations. -/
theorem predictor_price (s : Signed) (hc : 1<c.val) (n : ℕ) {γ δ : ℝ}
    (hp : S.patch.Branches S.kernel G) (hg : 0<γ) (hd : 0≤δ) (he : δ≤γ) :
    Bundle (ray G c) (marks G c δ) (native c) (namedCo s) (home S) (projected T k q (predictorRow (S:=S) s))
      0 n γ (|-(slip*Real.sqrt S.kernel.penalty)| * highBudget G S.patch S.kernel γ n) := by
  apply ((price_Q S s k hc n hp hg hd he).scale (-(slip*Real.sqrt S.kernel.penalty))).glue
  apply Eventually.of_forall
  intro B
  ext i j
  exact (predictor T k q s B i j).symm

/-- The three signed prices agree exactly with the genuine physical translation root. -/
theorem direct_anchor (s : Signed) (i : tile G f) :
    named S s i=PhysicalAffineScalarComparison.rowRoot S (directRow (S:=S) s i) := by
  simp only [named,PhysicalAffineScalarComparison.rowRoot,directRow,Sum.elim_inl,affine,add_zero,S.ratio.parent_signed S.patch.odd_side]

theorem predictor_anchor (s : Signed) (i : raw G c) :
    namedCo s i=PhysicalAffineScalarComparison.rowRoot S (predictorRow (S:=S) s i) := by
  simp only [namedCo,PhysicalAffineScalarComparison.rowRoot,predictorRow,Sum.elim_inr,affine,add_zero]

/-- All actual cut or uncropped ordinary raw signed rows have genuine finite-order germs. -/
theorem smooth (hp : S.patch.Branches S.kernel G) (hc : 1<c.val) {a b : ℝ} (hb : 0<b) (ha : 0≤a)
    (hW : Sheet T.up b a) (n : ℕ) (i : Rows.Receipt G S) (j : raw G f) :
    ContDiffAt ℝ n (fun B : Vec G c 1 => rawRows T k q B i j) 0 := by
  rcases i with ⟨⟨s,z|p⟩,a₀⟩
  · rcases z with ⟨⟨y,axes⟩,transported⟩
    let i : tile G f := (y,plaqEquiv axes,a₀)
    cases transported with
    | false =>
      have H := (direct_price T k q s hc n (γ:=1) zero_lt_one (δ:=0) le_rfl zero_le_one).smooth
      have hh := (evaluate i j).contDiff.contDiffAt.comp 0 H
      change ContDiffAt ℝ n (fun B => rawRows T k q B (directRow s i) j) 0 at hh
      simpa only [i,directRow,Equiv.symm_apply_apply] using hh
    | true =>
      have H := (transported_price T k q s hc n hb ha hW (δ:=0) le_rfl (ordering hb n).1.le).smooth
      have hh := (evaluate i j).contDiff.contDiffAt.comp 0 H
      change ContDiffAt ℝ n (fun B => rawRows T k q B (ConditionalAffineRowDifference.row s i) j) 0 at hh
      simpa only [i,ConditionalAffineRowDifference.row,Equiv.symm_apply_apply] using hh
  · let i : raw G c := (p.1,axisEquiv p.2,a₀)
    have H := (predictor_price T k q s hc n hp (γ:=1) zero_lt_one (δ:=0) le_rfl zero_le_one).smooth
    have hh := (evaluate i j).contDiff.contDiffAt.comp 0 H
    change ContDiffAt ℝ n (fun B => rawRows T k q B (predictorRow s i) j) 0 at hh
    simpa only [i,predictorRow,Equiv.symm_apply_apply] using hh

/-- Actual disjoint enumeration of the signed plaquettes, copied plaquettes and native predictors. -/
def rowIndex : (Signed × (tile G f ⊕ (tile G f ⊕ raw G c))) ≃ Rows.Receipt G S where
  toFun z := z.2.elim (directRow (S:=S) z.1)
    (Sum.elim (ConditionalAffineRowDifference.row (S:=S) z.1) (predictorRow (S:=S) z.1))
  invFun z := (z.1.1,z.1.2.elim (fun p => if p.2 then Sum.inr (.inl (p.1.1,plaqEquiv p.1.2,z.2))
    else Sum.inl (p.1.1,plaqEquiv p.1.2,z.2)) (fun b => .inr (.inr (b.1,axisEquiv b.2,z.2))))
  left_inv := by
    rintro ⟨s,⟨y,a,b⟩|⟨y,a,b⟩|⟨y,a,b⟩⟩ <;> simp [directRow,ConditionalAffineRowDifference.row,predictorRow]
    all_goals first | exact plaqEquiv.apply_symm_apply _ | exact axisEquiv.apply_symm_apply _
  right_inv := by
    rintro ⟨⟨s,⟨⟨y,a⟩,transported⟩|⟨y,a⟩⟩,b⟩
    · cases transported <;> simp [directRow,ConditionalAffineRowDifference.row]
      all_goals exact plaqEquiv.symm_apply_apply _
    · simp [predictorRow]
      exact axisEquiv.symm_apply_apply _

theorem rows_sum (v : Rows.Receipt G S→ℝ) :
    ∑ i, v i=∑ s : Signed, ((∑i : tile G f, v (directRow s i))+
      ((∑i : tile G f, v (ConditionalAffineRowDifference.row s i))+(∑i : raw G c, v (predictorRow s i)))) := by
  rw [←(rowIndex (G:=G) (S:=S)).sum_comp v,Fintype.sum_prod_type]
  simp only [Fintype.sum_sum_type]
  rfl

local notation "rows" => Rows.Receipt G S
local notation "homeRow" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "Coarse" => Vec G c 1

def sliceRows {ι : Type} (D : Coarse→Matrix rows (raw G f) ℝ) (z : ι→ rows) (B : Coarse) := (D B).submatrix z id

theorem transported_anchor (s : Signed) (i : tile G f) :
    homeRow (ConditionalAffineRowDifference.row s i)=named S s i := by
  simp only [named,PhysicalAffineScalarComparison.rowRoot,ConditionalAffineRowDifference.row,Sum.elim_inl,
    affine,add_zero,S.ratio.parent_signed S.patch.odd_side]

/-- Merge three genuinely disjoint physical Schur blocks, in both orientations.
The row and column charged sums are still over their actual fine input keys. -/
theorem stack (D : Coarse→Matrix rows (raw G f) ℝ) (n : ℕ) {δ γ a b e : ℝ}
    (ha : 0≤a) (hb : 0≤b) (he : 0≤e)
    (h₁ : ∀ s, Bundle (ray G c) (marks G c δ) (native c) (named S s) (home S) (sliceRows D (directRow s)) 0 n γ a)
    (h₂ : ∀ s, Bundle (ray G c) (marks G c δ) (native c) (named S s) (home S) (sliceRows D (ConditionalAffineRowDifference.row s)) 0 n γ b)
    (h₃ : ∀ s, Bundle (ray G c) (marks G c δ) (native c) (namedCo s) (home S) (sliceRows D (predictorRow s)) 0 n γ e) :
    Bundle (ray G c) (marks G c δ) (native c) homeRow (home S) D 0 n γ ((Fintype.card Signed:ℝ)*(a+(b+e))) := by
  let u := rowIndex (G:=G) (S:=S)
  have hD : ContDiffAt ℝ n D 0 := by
    let L : (rows→ raw G f→ℝ) ≃L[ℝ] Matrix rows (raw G f) ℝ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
    apply L.contDiff.contDiffAt.comp 0
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    obtain ⟨⟨s,z|z|z⟩,rfl⟩ := u.surjective i
    · exact (evaluate z j).contDiff.contDiffAt.comp 0 (h₁ s).smooth
    · exact (evaluate z j).contDiff.contDiffAt.comp 0 (h₂ s).smooth
    · exact (evaluate z j).contDiff.contDiffAt.comp 0 (h₃ s).smooth
  refine ⟨hD,fun l hl => ?_⟩
  let M := marks G c δ
  let W := (native c).weight γ
  let X := jet (ray G c) D l 0
  have jetSlice {ι : Type} [Fintype ι] (z : ι→ rows) (h : ContDiffAt ℝ n (sliceRows D z) 0) (i : ι) (j : raw G f) :
      X (z i) j = jet (ray G c) (sliceRows D z) l 0 i j := by
    unfold X
    rw [←FreeResolvent.TestD.entry (ray G c) l (smooth_of_le hD hl),←FreeResolvent.TestD.entry (ray G c) l (smooth_of_le h hl)]
    rfl
  have hr {ι : Type} [Fintype ι] {K : ℝ} (z : ι→ rows) (p : ι→Site c) (h : Bundle (ray G c) M (native c) p (home S) (sliceRows D z) 0 n γ K)
      (eq : ∀ i,homeRow (z i)=p i) (i : ι) : M.pay l (homeRow (z i))*(∑ j,W (homeRow (z i)) (home S j)*|X (z i) j|)≤K := by
    simp_rw [eq,jetSlice z h.smooth]
    exact (h.bound l hl).row.rows i
  have hc {ι : Type} [Fintype ι] {K : ℝ} (z : ι→ rows) (p : ι→Site c) (h : Bundle (ray G c) M (native c) p (home S) (sliceRows D z) 0 n γ K)
      (eq : ∀ i,homeRow (z i)=p i) (j : raw G f) : M.pay l (home S j)*(∑ i,W (home S j) (homeRow (z i))*|X (z i) j|)≤K := by
    simp_rw [eq,jetSlice z h.smooth]
    exact (h.bound l hl).col.rows j
  have hs : (1:ℝ)≤Fintype.card Signed := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card Signed)
  have htot := le_mul_of_one_le_left (add_nonneg ha (add_nonneg hb he)) hs
  constructor <;> constructor
  · intro i
    obtain ⟨⟨s,z|z|z⟩,rfl⟩ := u.surjective i
    · exact ((hr _ _ (h₁ s) (fun i => (direct_anchor s i).symm) z).trans (le_add_of_nonneg_right (add_nonneg hb he))).trans htot
    · exact ((hr _ _ (h₂ s) (transported_anchor s) z).trans (by linarith : b≤a+(b+e))).trans htot
    · exact ((hr _ _ (h₃ s) (fun i => (predictor_anchor s i).symm) z).trans (by linarith : e≤a+(b+e))).trans htot
  · intro j
    let v := fun i : rows => W (home S j) (homeRow i)*|X i j|
    change M.pay l (home S j)*(∑i,v i)≤_
    rw [rows_sum v,Finset.mul_sum]
    calc _ ≤ ∑ _s : Signed,(a+(b+e)) := by
          apply Finset.sum_le_sum
          intro s _
          rw [mul_add,mul_add]
          exact add_le_add (hc _ _ (h₁ s) (fun i => (direct_anchor s i).symm) j)
            (add_le_add (hc _ _ (h₂ s) (transported_anchor s) j) (hc _ _ (h₃ s) (fun i => (predictor_anchor s i).symm) j))
      _ = _ := by
        simp [nsmul_eq_mul]
        ring

def price (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (a b : ℝ) :=
  (Fintype.card Signed:ℝ) * (|slip*Real.sqrt p.direct| * lowBudget G P K (wider b n) n +
    (|slip| * phasePrice G P K n a b + |-(slip*Real.sqrt K.penalty)| * highBudget G P K (wider b n) n))

/-- Full attached true ordinary raw response, normalized for its original permit. -/
theorem ordinary (hc : 1<c.val) (n : ℕ) {b a δ : ℝ}
    (hb : 0<b) (ha : 0≤a) (hW : Sheet T.up b a) (hp : S.patch.Branches S.kernel G)
    (hd : 0≤δ) (he : δ≤tier b n) :
    Bundle (ray G c) (marks G c δ) (native c) homeRow (home S) (rawRows T k q) 0 n (wider b n)
      (price G S.patch S.kernel T.high n a b) := by
  have hv := (ordering hb n).1.trans_le (ordering hb n).2.1
  have hr := he.trans (ordering hb n).2.1
  exact stack _ n (mul_nonneg (abs_nonneg _) (low_nn n _ _ hv)) (mul_nonneg (abs_nonneg _) (phase_nn _ _ _ hb ha))
    (mul_nonneg (abs_nonneg _) (high_nn n _ _ hv))
    (fun s => direct_price T k q s hc n hv hd hr) (fun s => transported_price T k q s hc n hb ha hW hd he)
    (fun s => predictor_price T k q s hc n hp hv hd hr)

private theorem zero_block {ι : Type} [Fintype ι] (D : Coarse→Matrix ι (raw G f) ℝ) (z : ι→Site c)
    (h : ∀ B,D B=0) (δ γ : ℝ) (n : ℕ) : Bundle (ray G c) (marks G c δ) (native c) z (home S) D 0 n γ 0 := by
  let Z := fun _ : Coarse => (0:Matrix ι (raw G f) ℝ)
  have hz : Bundle (ray G c) (marks G c δ) (native c) z (home S) Z 0 n γ 0 := by
    refine ⟨contDiffAt_const,fun l _ => ?_⟩
    have hzero : (marks G c δ).Bill (native c) z (home S) l γ 0 (0 : Matrix ι (raw G f) ℝ) :=
      ⟨Mark.Rates.zero le_rfl,Mark.Rates.zero le_rfl⟩
    by_cases hh : l=[]
    · subst l; rw [zeroth]; exact hzero
    · rw [show Z=(fun _ : Coarse => (0:Matrix ι (raw G f) ℝ)) from rfl,jet_const _ _ hh]
      exact hzero
  exact hz.glue (Eventually.of_forall fun B => (h B).symm)

/-- The full raw physical source-column error. The only paid branch is the
transported signed plaquette; the direct and predictor branches are zero at
every background, before differentiation, on these original coordinates. -/
theorem tail (R : ℕ) (hc : 1<c.val) (n : ℕ) {b a δ : ℝ} (hb : 0<b) (ha : 0≤a)
    (hW : Sheet T.up b a) (hd : 0≤δ) (he : δ≤tier b n) :
    Bundle (ray G c) (marks G c δ) (native c) homeRow (home S)
      (fun B => rawRows T k all B-rawRows T k (shorter R) B) 0 n (wider b n)
      ((Fintype.card Signed:ℝ)*(|slip| * (Real.exp (-(b/4)*R)*phasePrice G S.patch S.kernel n a b))) := by
  let D := fun B => rawRows T k all B-rawRows T k (shorter R) B
  have h₁ s (B : Coarse) : sliceRows D (directRow s) B=0 := by
    ext i j
    change rawRows T k all B (directRow s i) j - rawRows T k (shorter R) B (directRow s i) j = 0
    rw [direct,direct,sub_self]
  have h₃ s (B : Coarse) : sliceRows D (predictorRow s) B=0 := by
    ext i j
    change rawRows T k all B (predictorRow s i) j - rawRows T k (shorter R) B (predictorRow s i) j = 0
    rw [predictor,predictor,sub_self]
  have h₂ s := (ConditionalAffineRowDifference.price T k s R n hc hb ha hW hd he).glue
    (Eventually.of_forall (fun B => show ConditionalAffineRowDifference.difference T k s R B=sliceRows D (ConditionalAffineRowDifference.row s) B from rfl))
  have hh := stack D n (a:=0) (e:=0) le_rfl
    (mul_nonneg (abs_nonneg slip) (mul_nonneg (Real.exp_pos _).le (phase_nn _ _ _ hb ha))) le_rfl
    (fun s => zero_block _ (named S s) (h₁ s) δ (wider b n) n) h₂
    (fun s => zero_block _ (namedCo s) (h₃ s) δ (wider b n) n)
  simpa only [zero_add,add_zero] using hh

end YM.Integration.PhysicalAffineScalarOrdinaryColumns
end
