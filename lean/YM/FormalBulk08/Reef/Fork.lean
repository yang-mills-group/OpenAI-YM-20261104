import YM.FormalBulk08.Reef.Mount

/-! Transport Haar charge to the formal chart Jacobian. Generic for
pointwise fibre chart homotopies. The proof by compact image tests avoids having to
prescribe equal additive measures on spaces with differing Orthonormal basis. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Wick Orb Jets Function Matrix Filter Set MeasureTheory Metric Precision Work.F05 RG Wilson Lattice Tree
open scoped BigOperators ContDiff Topology ENNReal
variable {V I : Type} [Fintype V] [Fintype I]

private lemma tells {E : Type} [MetricSpace E] [MeasureSpace E] [BorelSpace E]
   [IsFiniteMeasureOnCompacts (volume : Measure E)] [Measure.IsOpenPosMeasure (volume : Measure E)] [ProperSpace E]
   (x:E) (s:Set E) (f g : E→ℝ) (hh : s∈𝓝 x)
   (e : ∀ U : Set E, IsCompact U → U⊆s → (∫⁻ y in U, ENNReal.ofReal (f y))=∫⁻ y in U, ENNReal.ofReal (g y))
   (hf : ContinuousAt f x) (hg : ContinuousAt g x) (p : 0≤f x): g x≤ f x := by
  -- contradiction via strict interval separation
  by_contra! h
  obtain ⟨a,ha,ha'⟩:= exists_between h; obtain ⟨b,hb,hb'⟩:= exists_between ha'
  have ht := hh
  let Q := s ∩ {y| f y < a} ∩ {y| b < g y}
  have ht : Q∈𝓝 x := inter_mem (inter_mem hh (hf.eventually (gt_mem_nhds ha))) (hg.eventually (lt_mem_nhds hb'))
  obtain ⟨r,hr,H⟩:=nhds_basis_closedBall.mem_iff.mp ht
  let U:=closedBall x r; have hu : IsCompact U:= isCompact_closedBall ..
  have hp : 0<volume U := lt_of_lt_of_le (isOpen_ball.measure_pos volume ⟨x,mem_ball_self hr⟩) (measure_mono ball_subset_closedBall)
  apply (e U hu (fun y hy=>(H hy).1.1)).not_lt
  calc _ ≤ ∫⁻ _ : E in U, ENNReal.ofReal a := setLIntegral_mono' hu.measurableSet fun y hy=> ENNReal.ofReal_le_ofReal (show f y<a from (H hy).1.2).le
       _ < ∫⁻ _:E in U, ENNReal.ofReal b := by simp only [lintegral_const, Measure.restrict_apply_univ]; exact ENNReal.mul_lt_mul_left hp.ne' hu.measure_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (p.trans ha.le)).mpr hb)
       _ ≤ _ := setLIntegral_mono' hu.measurableSet fun y hy=> ENNReal.ofReal_le_ofReal (show b<g y from (H hy).2).le
-- correction f x=0 possible if jac det=0 => use nonnegative version

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (P : ChartRatio G) (h : LocalRatio P)
include h

private lemma pointee (q : F.Slice G→ F.Slice G) (hm : MeasurePreserving q (F.order G) (F.order G)) (hi : Injective q)
    (A : AxisChart G F→AxisChart G F) (y : AxisChart G F) (H : ∀ᶠ z in 𝓝 y,z∈parcel F P ∧ A z∈parcel F P ∧ ContDiffAt ℝ 2 A z ∧ exposure F 0 (A z)=q (exposure F 0 z)) :
      toll F P y=|(fderiv ℝ A y).det| * toll F P (A y) := by
   let U := {z| z∈parcel F P ∧ A z∈parcel F P ∧ ContDiffAt ℝ 2 A z ∧ exposure F 0 (A z)=q (exposure F 0 z)}
   let g z:=|(fderiv ℝ A z).det| * load F P (A z)
   have he (C:Set (AxisChart G F)) (hc:IsCompact C) (hg:C⊆U) : (∫⁻ z in C,ENNReal.ofReal (load F P z))=∫⁻ z in C,ENNReal.ofReal (g z) := by
      have hh (z:AxisChart G F) (hz:z∈C) : HasFDerivAt A (fderiv ℝ A z) z := ((hg hz).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
      have hp : InjOn A C:= fun x hx y hy e=> exposure_inj F h 0 (hg hx).1 (hg hy).1 <| hi <| (hg hx).2.2.2.symm.trans ((congr_arg (exposure F 0) e).trans (hg hy).2.2.2)
      let D:=A '' C
      have hd : IsCompact D := hc.image_of_continuousOn (fun x hx=> (hh x hx).continuousAt.continuousWithinAt)
      have hx : D⊆parcel F P := by rintro _ ⟨x,hx,rfl⟩; exact (hg hx).2.1
      have hv : Continuous (exposure F (0:Bid.Dir G c)) := (exposure_continuous F).comp (f:=fun x=>(0,x)) (continuous_const.prodMk continuous_id)
      have hu : exposure F 0 '' D=q '' (exposure F 0 '' C) := by unfold D; rw [image_image,image_image]; apply EqOn.image_eq;intro x hx; exact (hg hx).2.2.2
      have hs := hm.measure_preimage ((hd.image hv).measurableSet.nullMeasurableSet (μ:=F.order G))
      rw [show q ⁻¹' (exposure F 0 '' D)=exposure F 0 '' C by rw [hu,hi.preimage_image]] at hs
      calc _ = _ := (order_exposed F h (0:Bid.Dir G c) C hc fun x hx=>(hg hx).1).symm
           _ = (F.order G) (exposure F (0:Bid.Dir G c) '' D) := hs
           _ = ∫⁻ z in D, ENNReal.ofReal (load F P z):= order_exposed F h _ D hd hx
           _ = ∫⁻ z in C, ENNReal.ofReal |(fderiv ℝ A z).det| * ENNReal.ofReal (load F P (A z)) := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hc.measurableSet (fun z hz=> (hh z hz).hasFDerivWithinAt) hp _
           _ = _ := by simp only [g,ENNReal.ofReal_mul (abs_nonneg _)]
   have hy : y∈U := H.self_of_nhds; have hr:=hy.2.2.1
   have ha : ContinuousAt g y := ContinuousAt.mul (ContinuousAt.abs (ContinuousLinearMap.continuous_det.continuousAt.comp (hr.fderiv_right (m:=1) (by norm_num)).continuousAt)) ((load_cont F h hy.2.1).comp hr.continuousAt)
   have hk : load F P y=g y := le_antisymm (tells _ U _ _ H (fun U hs hu=>(he U hs hu).symm) ha (load_cont F h hy.1) (mul_nonneg (abs_nonneg _) (load_pos F h hy.2.1).le)) (tells _ U _ _ H he (load_cont F h hy.1) ha (load_pos F h hy.1).le)
   unfold g at hk; simp_rw [load_eq] at hk; rw [mul_left_comm _ _ (Work.F05.toll F P (A y))] at hk; exact mul_left_cancel₀ (pow_ne_zero _ h.scale.ne') hk
omit h
private lemma lay_det {V J : Type} [DecidableEq V] [Fintype V] [Fintype J]
    (X : AxisChart G F≃L[ℝ] Jets.Rays V) (A : Jets.Rays (V⊕J)→ Jets.Rays V) (p : Jets.Rays (V⊕J)) (hp : DifferentiableAt ℝ A p) :
       let Y:=p ∘ Sum.inl; let W:=p ∘ Sum.inr
       (dollars A p).det=(fderiv ℝ (fun x => X.symm (A (Sum.elim (X x) W))) (X.symm Y)).det := by
   classical
   intro Y W
   let m:Rays V→L[ℝ] Rays (V⊕J) := LinearMap.toContinuousLinearMap {
      toFun x:=Sum.elim x 0
      map_add' x y:=funext (fun j=> by cases j <;> simp)
      map_smul' c x:=funext (fun j=> by cases j <;> simp) }
   let B:=fun x:Rays V=>A (Sum.elim x W)
   have he : HasFDerivAt B ((fderiv ℝ A p).comp m) Y := by
      let f:=fun x : Rays V=> Sum.elim x W
      have hy : f Y=p:= by unfold f Y W; ext i; cases i <;> rfl
      have hf : HasFDerivAt f m Y := by
         rw [show f=(⇑m+(fun _:Rays V=>Sum.elim (0:Rays V) W) : Rays V→Rays (V⊕J)) by
             ext i j; change f i j=m i j+_;cases j <;> simp [f,m]]
         simpa using! m.hasFDerivAt.add_const (Sum.elim (0:Rays V) W)
      have hh : HasFDerivAt A (fderiv ℝ A p) (f Y) := hy.symm ▸ hp.hasFDerivAt
      exact hh.comp Y hf
   have hh : dollars A p=LinearMap.toMatrix' (fderiv ℝ B Y).toLinearMap := by
      rw [he.fderiv,← dollars_act A p hp]; ext i j; simp only [Matrix.submatrix_apply, id_eq, LinearMap.toMatrix'_apply];
      change fderiv ℝ A p _ i= fderiv ℝ A p (m _) i
      apply congr_arg (fun u=> fderiv ℝ A p u i); ext k; cases k <;> simp [m,Pi.single_apply]
   have hY : HasFDerivAt B (fderiv ℝ B Y) (X (X.symm Y)) := by rw [X.apply_symm_apply];exact he.differentiableAt.hasFDerivAt
   have ht:= X.symm.toContinuousLinearMap.hasFDerivAt.comp (X.symm Y) (hY.comp (X.symm Y) X.toContinuousLinearMap.hasFDerivAt)
   rw [hh,LinearMap.det_toMatrix'];
   have ht' : fderiv ℝ (fun x => X.symm (A (Sum.elim (X x) W))) (X.symm Y) = _ := ht.fderiv
   rw [ht']; exact (LinearMap.det_conj (fderiv ℝ B Y).toLinearMap X.symm.toLinearEquiv).symm

variable (A:Rays (Pine G S F ⊕ I)→ Rays (Pine G S F)) (f : Rays I → F.Slice G→ F.Slice G)
    (hm : ∀ i, MeasurePreserving (f i) (F.order G) (F.order G))
    (hi : ∀ i, Injective (f i))
    (H : ∀ᶠ z in 𝓝 0, exposure F 0 (stand G F (A z))=f (z ∘ Sum.inr) (exposure F 0 (stand G F (z ∘ Sum.inl))))
    (ha : ContDiffAt ℝ ∞ A 0) (hp : A 0=0)
include h hm hi H ha hp

lemma root_pay : ∀ᶠ z in 𝓝 0, sap F P (z ∘ Sum.inl)=|(dollars A z).det| * sap F P (A z) := by
    let X : Rays (Pine G S F)≃L[ℝ] _ := stand G F
    have hv : ∀ᶠ z in 𝓝 0, ContDiffAt ℝ 2 A z ∧ exposure F 0 (X (A z))= f (z ∘ Sum.inr) (exposure F 0 (X (z ∘ Sum.inl))) ∧ X (A z)∈parcel F P ∧ X (z ∘ Sum.inl)∈parcel F P := by
       have h1 : Tendsto (fun z:Rays (Pine G S F⊕I)=> A z) (𝓝 0) (𝓝 0):=hp ▸ ha.continuousAt.tendsto
       have h2 : Tendsto (fun z:Rays (Pine G S F⊕I)=>z ∘ Sum.inl) (𝓝 0) (𝓝 0):= tendsto_pi_nhds.mpr fun i=> (continuous_apply (Sum.inl i)).tendsto (0:Rays (Pine G _ F⊕I))
       have hX : Tendsto X (𝓝 0) (𝓝 0) := by simpa using X.continuous.tendsto 0
       exact ((ha.of_le (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by exact WithTop.coe_le_coe.mpr le_top)).eventually (by simp)).and (H.and (((hX.comp h1).eventually (parcel_zero F h)).and ((hX.comp h2).eventually (parcel_zero F h))))
    filter_upwards [eventually_eventually_nhds.mpr hv] with p hh
    let y:=p ∘ Sum.inl; let q:=p ∘ Sum.inr; let S:=fun x=>Sum.elim (X.symm x) q; let B x:= X (A (S x));
    have hy : S (X y)=p := by ext i; cases i <;> simp [S,X,y,q]
    have hs (x): ContDiffAt ℝ 2 S x := contDiffAt_pi.mpr fun i=> by cases i; exacts [contDiffAt_pi.mp X.symm.contDiff.contDiffAt _,contDiffAt_const]
    have he: (dollars A p).det= (fderiv ℝ B (X y)).det := lay_det F X.symm _ _ (hh.self_of_nhds.1.differentiableAt (by norm_num))
    unfold sap; rw [he]; have hb : B (X y)=X (A p) := by unfold B; rw [hy]
    rw [← show B (X y)=stand G F (A p) from hb]; apply pointee F P h (f q) (hm q) (hi q) B (X y)
    filter_upwards [(show Tendsto S (𝓝 (X y)) (𝓝 p) from hy ▸ (hs (X y)).continuousAt.tendsto).eventually hh] with z hz
    obtain ⟨hd,hp,hx,hu⟩:=hz
    have hl : X ((S z) ∘ Sum.inl)=z := X.apply_symm_apply _
    rw [hl] at hu hp
    exact ⟨hu,hx,X.contDiff.contDiffAt.comp z (hd.comp z (hs z)),hp⟩
lemma bread : ∃ M : Matrix (Pine G S F) (Pine G S F) ℝ,
     dollars A 0*M=1 ∧ ∀ᶠ z in 𝓝 0, sap F P (z ∘ Sum.inl) = sap F P (A z) * (M.det*(dollars A z).det) := by
   let L:= dollars A 0
   have hx:=root_pay F P h A f hm hi H ha hp
   have hy := hx.self_of_nhds; rw [show (0:Rays (Pine G _ F⊕I)) ∘ Sum.inl=0 from rfl,sap_root F P h,hp,sap_root F P h,mul_one] at hy
   have he : L.det ≠ 0 := by rw [← abs_pos, ← show 1=|L.det| from hy]; exact one_pos
   let M:=L⁻¹
   have hQ : L*M=1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr he)
   have ht : M.det*L.det=1 := by rw [mul_comm,←Matrix.det_mul,hQ,Matrix.det_one]
   have hg : |M.det|=1 := by
     apply mul_right_cancel₀ (b:=|L.det|) (abs_pos.mpr he).ne'
     rw [← abs_mul,ht,abs_one,← show 1=|L.det| from hy,mul_one]
   refine ⟨M,hQ,?_⟩
   have hc : ContinuousAt (fun z=> M.det*(dollars A z).det) 0 := continuousAt_const.mul (merch A ha).continuousAt
   filter_upwards [hc.eventually (lt_mem_nhds (show 0<M.det*(dollars A 0).det by rw [show dollars A 0=L from rfl,ht]; exact one_pos)),hx] with z hz hu
   rw [hu,mul_comm (sap F P (A z)),← abs_of_nonneg (show 0≤ M.det*(dollars A z).det from le_of_lt hz),abs_mul,hg,one_mul]
end YM.FormalBulk08.Reef
