import YM.FormalBulk08.Flat.Slice
import Mathlib.Analysis.Matrix.Order

/-! Covariance restriction exact at finite periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f} {j : ℕ}

lemma visits (x : BaseSites G f) :
    patron G (fixRoot S)*ᵥ (gradientA G f x)=patron G (fetch S) *ᵥ x-curryG G S *ᵥ x := by
  ext i
  obtain ⟨a,u,k⟩:=i; rw [vac_only u]
  simp only [Pi.sub_apply,curry_at]; rw [show (patron G (fetch S) *ᵥ x) (a,vac,k) = x (S.ratio.embed a, vac,k) from
    (congr_fun (paint_eats _ _ k) (a,vac)).trans (congr_fun (fetch_lands _) (a,vac))]
  rw [first_uniform, ← patron_fee]
  change atPaint (patron G (fixRoot S) *ᵥ (patron G (d 0 f)*ᵥ x)) k (a,vac) = _
  rw [paint_eats,paint_eats]; exact psi_proj S _ (a,vac)

lemma forests_kill (F : Forest S.ratio) : hang G S F * spreadM (G:=G) S = 0 := by
  let B:= butt G c f
  let R:= brim G c f
  let T:=patron G (fixRoot S)
  let X:= patron G (d 0 f)
  have H (x : BaseSites G f) :
      let p:= spreadM S*ᵥ x
      B*ᵥ p= -(X*ᵥ x) ∧ R*ᵥ p= -(curryG G S*ᵥ x) := by
    intro p
    unfold B R p; rw [helmet_butt, helmet_brim, parliament S, helmet_ear, first_uniform, ← patron_fee,sliceX,sliceY]; exact ⟨rfl,rfl⟩
  have hm : lead G S F * spreadM (G:=G) S= 1 := by
    apply mat_confirm; intro v
    let p:= spreadM S*ᵥ v
    have hh := congr_arg (fun z:Lines G c 0→ℝ=>z) (visits (S:=S) v)
    change patron G (fixRoot S) *ᵥ (gradientA G f v)=_ at hh
    rw [first_uniform, ← patron_fee] at hh
    obtain ⟨hv,hw⟩:= H v
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    funext ⟨i,e,k⟩; rw [vac_only e]
    rw [show (lead G S F *ᵥ p) _ = _ from lead_price F p (i,vac,k)]
    change integralLink i _ (atPaint (B*ᵥ p) k) - (T*ᵥ (B*ᵥ p)+R*ᵥ p) _ = _
    change B*ᵥ p= _ at hv; change R*ᵥ p= _ at hw
    rw [hv,hw,Matrix.mulVec_neg]
    change T *ᵥ (X *ᵥ v)= _ at hh
    rw [hh]
    have he : (atPaint (-(X*ᵥ v)) k) = -(d 0 f*ᵥ atPaint v k):= by rw [← paint_eats]; rfl
    rw [he,map_neg, telescopes, Forest.hike_root]
    have hg : (patron G (fetch S) *ᵥ v) (S.ratio.parent i,vac,k)= v (S.ratio.embed (S.ratio.parent i),vac,k) :=
      (congr_fun (paint_eats _ _ _) (_,vac)).trans (congr_fun (fetch_lands _) _)
    dsimp only [Pi.sub_apply,Pi.neg_apply,Pi.add_apply,atPaint]; rw [hg]; abel
  have hv : imprint G S F * spreadM (G:=G) S=0 := by
    change (B+X*lead G S F)*spreadM S=0
    rw [Matrix.add_mul, Matrix.mul_assoc X,hm,Matrix.mul_one]; apply mat_confirm
    intro v; rw [Matrix.add_mulVec,← Matrix.mulVec_mulVec, Matrix.zero_mulVec,(H v).1, neg_add_cancel]
  rw [hang,Matrix.mul_assoc,hv,Matrix.mul_zero]

-- exhibit a (second, noncanonical) section of hang
lemma trail_null (F : Forest S.ratio) (R : Alive G S F → ℝ) :
    patron G (trails S F) *ᵥ ((dropRoot G S F)ᵀ*ᵥ R)=0 := by
  ext x
  let k:=x.2.2
  let v:=(dropRoot G S F)ᵀ*ᵥ R
  have ht (i) (hi : leaf S.ratio i) : atPaint v k (( (F.up i).used i).1,coord ((F.up i).used i).2)=0 := by
    apply bring_dead
    unfold lives
    rw [show axisEquiv.symm (coord _) =_ from axisEquiv.symm_apply_apply _]
    exact fun hk=> hk ((F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩)
  have hv (i) : integralLink i (F.hike i) (atPaint v k)=0 := by
    induction i using Forest.hike.induct F with
    | case1 i hi he =>
      rw [Forest.hike,dif_pos hi]
      change (if (F.up i).neg then -_ else _)+integralLink _ _ _=0
      dsimp only; rw [ht i hi,he]; simp
    | case2 i hi => rw [Forest.hike,dif_neg hi]; rfl
  exact (roots_pictured ..).trans (hv _)
lemma section_exists (F : Forest S.ratio) : ∃ V : Matrix (Bodies G c f) (Alive G S F) ℝ, hang G S F*V=1 := by
  apply Exists.intro
    (LinearMap.toMatrix' ((cash (helmets G c f)).toLinearMap ∘ₗ
      ((dropRoot G S F)ᵀ.mulVecLin.prod (-(patron G (fixRoot S)*(dropRoot G S F)ᵀ).mulVecLin))))
  apply mat_confirm; intro v
  let b:= (dropRoot G S F)ᵀ *ᵥ v; let e:= -(patron G (fixRoot S) *ᵥ b)
  let u:= (cash (helmets G c f)) (b,e)
  rw [← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
  change hang G S F *ᵥ ((cash (helmets G c f)) (b,-((patron G (fixRoot S) * (dropRoot G S F)ᵀ)*ᵥ v))) = _
  rw [← Matrix.mulVec_mulVec]
  change hang G S F *ᵥ u=v
  have hv' : butt G c f *ᵥ u=b := rear_cost ..
  have he' : brim G c f *ᵥ u=e := by unfold u; rw [helmet_brim,helmet_ear,sliceY]; rfl
  have hX : lead G S F *ᵥ u=0 := by simp only [lead,Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,hv',he']; rw [show patron G (trails S F)*ᵥ b=0 from trail_null ..]; unfold e; simp
  rw [hang,← Matrix.mulVec_mulVec,imprint, Matrix.add_mulVec,hv',← Matrix.mulVec_mulVec,hX,Matrix.mulVec_zero,add_zero]; unfold b; rw [Matrix.mulVec_mulVec,returns,Matrix.one_mulVec]

def testPrecision (G : Gauge) (S : StepData c f) (F : Forest S.ratio) (V : Train j) :=
    let Q := (dropRoot G S F)ᵀ
    let B:=patron G (Precision.K ((pink S.kernel.penalty V).acts f))
    let M:=patron G (Precision.probe S)*Q
    Qᵀ*B*Q+ S.kernel.penalty • (Mᵀ*M)
lemma meat_factor (S : StepData c f) (F : Forest S.ratio) (t : S.Choices) (V : Train j) :
    let P:= postroom (G:=G) S t (Stationary.inch S.patch.L); let L:=hang G S F
    meat S t V=Lᵀ*testPrecision G S F V*L+Pᵀ*P := by
  intro P L
  let Q := (dropRoot G S F)ᵀ; let X:=imprint G S F; let U:=fortune G S; let H:= (pink S.kernel.penalty V).acts f
  let B:= patron G (Precision.K H); let M:=patron G (probe S)*Q
  have he : Q*L=X := inject_out _
  have ht : M*L= -U := by unfold M; rw [Matrix.mul_assoc,he]; exact hits_tree _
  change _=Lᵀ*(Qᵀ*B*Q+_ • (Mᵀ*M))*L + _
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
  have hp : Lᵀ*(Qᵀ*B*Q)*L=Xᵀ*B*X:=by rw [← he,Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hg : Lᵀ*(Mᵀ*M)*L=Uᵀ*U := by rw [← Matrix.mul_assoc Lᵀ,← Matrix.transpose_mul, ht, Matrix.mul_assoc,ht]; simp
  rw [hp,hg,show Xᵀ*B*X=_ from base_tree F H]; rfl

lemma inside_quadratic {a b u : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype u] [DecidableEq u]
    (H T : Matrix b b ℝ) (Q : Matrix b u ℝ) (R : Matrix u b ℝ) (L : Matrix a b ℝ) (V : Matrix a a ℝ)
    (ht : H*T=1) (hx : H=Lᵀ*V*L+Rᵀ*R) (hq : IsUnit (R*Q).det) (hp : L*Q=0) (hl : ∃ x : Matrix b a ℝ,L*x=1) :
    V*(L*T*Lᵀ)=1 := by
  obtain ⟨x,hx'⟩:=hl
  let M:= (R*Q)⁻¹
  let N:=x-Q*M*R*x
  have hh : L*N=1 := by unfold N; simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hp,hx',Matrix.zero_mul,sub_zero]
  have hg : R*N=0 := by unfold N; rw [Matrix.mul_sub]; simp only [← Matrix.mul_assoc]; rw [show R * Q * M=1 from Matrix.mul_nonsing_inv _ hq]; simp
  have hh' : Nᵀ * H=V*L := by rw [hx, Matrix.mul_add]; simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, hh,hg, Matrix.transpose_one,Matrix.transpose_zero,Matrix.one_mul, Matrix.zero_mul,add_zero]
  calc
    _ = Nᵀ * (H*T) * Lᵀ := by rw [← Matrix.mul_assoc Nᵀ, hh']; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ht,Matrix.mul_one,← Matrix.transpose_mul,hh, Matrix.transpose_one]
lemma triangle_pin (S : StepData c f) (h : S.patch.Branches S.kernel G) (t : S.Choices) (V : Train j) (F : Forest S.ratio)
    {T} (hv : meat (G:=G) S t V*T=1) : testPrecision G S F V*(hang G S F*T*(hang G S F)ᵀ)=1 := by
  apply inside_quadratic _ _ (spreadM S (G:=G)) _ _ _ hv (meat_factor ..) _ (forests_kill F) (section_exists F)
  rw [fired _ _ h]; exact fund_det (grenade_safe _ (Stationary.inch_pos _))

lemma semi (S : StepData c f) (F : Forest S.ratio) (V : Train j) (hj : 4≤j) :
    (testPrecision G S F V).PosSemidef := by
  let k:= S.kernel.penalty
  obtain ⟨σ,A,ε,hσ,hA,hε,a,h⟩:= affiliates _ hj k S.kernel.penalty_pos
  obtain ⟨T,ht,H⟩:= h V
  let C:= T.B.metric.acts f
  have hx : C.PosSemidef := Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨(by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using (H f).symmetric.1),fun x=> by
    rw [star_trivial]; have hv := (H f).uniform.1 x
    refine le_trans ?_ hv.1
    apply mul_nonneg hε.le; exact Finset.sum_nonneg (fun i _=> mul_self_nonneg _)⟩
  have he : (patron G C).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,fun x=>?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial,← patron_star]; exact congr_arg (patron G) (H f).symmetric.1
    rw [star_trivial,dotColor,patron_fee]; simp_rw [Stationary.uniformC]
    apply Finset.sum_nonneg; intro a _; simpa only [star_trivial] using hx.dotProduct_mulVec_nonneg (parts G 2 (Stationary.arm G f 2 x) a)
  let U : Matrix (Lines G f 1) (Lines G f 1) ℝ:= patron G (Precision.K ((pink k V).acts f))
  have hp : U.PosSemidef := by unfold U; rw [← T.stands,Precision.K,patron_mul,patron_mul,patron_star]; exact he.conjTranspose_mul_mul_same _
  let X:= (dropRoot G S F)ᵀ
  let M:=patron G (probe S)*X
  have hk: 0≤k:= S.kernel.penalty_pos.le
  exact (hp.conjTranspose_mul_mul_same X).add ((Matrix.posSemidef_conjTranspose_mul_self M).smul hk)
lemma definite (S : StepData c f) (h : S.patch.Branches S.kernel G) (t : S.Choices) (V : Train j) (F : Forest S.ratio)
    {T} (hv : meat (G:=G) S t V*T=1) (hj : 4≤j) : (testPrecision G S F V).PosDef :=
  ((semi S F V hj).posDef_iff_isUnit).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (triangle_pin S h t V F hv)))
end YM.FormalBulk08.Flat
