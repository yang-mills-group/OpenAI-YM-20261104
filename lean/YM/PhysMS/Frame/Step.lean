import YM.PhysMS.Frame.Measured
import YM.PhysMS.Frame.ShellIteration
import YM.Pert.Scale.Adjust

/-! # Measure cocycle: cost from coherent leading positions data

Works for a filtration stage *as a whole*, no need of orthogonality by grading here. Control
both directions of the matching frame cost **in the full finite horizon**. Read the Gram with
the entire mixing and normalization included. Doing a top-column operation independently at
each higher horizon might not be stable. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Set Filter Function Spec OPE OPE.Levy Climb Maxwell YM.Push.FiniteDetection.Free Trace.Pilot
open scoped Topology BigOperators ContDiff Classical ComplexOrder
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "engine" a => Pert.Scale.gear C.labels d a
local notation "E0" a => Pert.Scale.gear C.labels d a

section coherent
/-- Pull actual two-point to query frame, at relative separation x. -/
private def twoAt (d : ℕ) (r : ℝ) (x : Points 2) : (Bel C.book).Field d →ₗ[ℂ] (Bel C.book).Field d →ₗ[ℂ] ℂ :=
   OPE.Levy.linear₂ ((S.classMoment S (fun _ : Fin 2=>d) (r • x)).compLinearMap (fun _=> (J r d).toLinearMap))
private def freeAt (d : ℕ) (C : Family G) (x : Points 2) : (Bel C.book).Field d →ₗ[ℂ] (Bel C.book).Field d →ₗ[ℂ] ℂ :=
   OPE.Levy.linear₂ ((Bel C.book).classMoment (Bel C.book) (fun _=>d) x)

private lemma gram_at (r : ℝ) (x : Points 2) (u v : D) :
    twoAt J d r x u v = OPE.Levy.pair d S (r • x) (J r d u) (J r d v) := by
  apply DFunLike.congr_arg (S.classMoment S (fun _=>d) _)
  exact funext fun i=> by fin_cases i <;> rfl

/-- Reflection form and free dilation commute; no hypothesis on an eventual physical scheme.
    These are the *same* H and conjugation used for `J`. -/
lemma flip_dilation (t : ℝ) (u : D) : reflect d (Pert.Scale.gear C.labels d t u) = (E0 t) (reflect d u) := by
  unfold Levy.reflect
  rw [show (Bel C.book).conj _ _ _ = (E0 t) _ from Pert.Scale.gear_conj C.labels u t]
  -- signed mirror just the free action in that subgroup
  change Pert.Rigid.wear C.labels d (Signed.mirror timeAxis) ((engine t) _) = (engine t) (Pert.Rigid.wear C.labels d (Signed.mirror timeAxis) _)
  simp_rw [Pert.Rigid.wear_ride]; exact Pert.Scale.gear_spin ..

lemma flip_coupled (r) (hr : Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r d)) (u : D) :
    J r d (reflect d u) = S.mirror F.room.kernel.spin d (Signed.mirror timeAxis) (S.conj F.room.kernel.spin d (J r d u)) := by
  rw [Levy.reflect, hr.1, hr.2]

private lemma step_path (v : D) : Continuous fun a:ℝ=> (engine a) v := by
  let V:= Extra.FD.recorded C.labels d
  conv => arg 1; ext x; rw [← V.b.sum_repr v,map_sum]
  simp_rw [map_smul,Pert.Scale.rare]
  fun_prop

private lemma varies {I : Type*} {l : Filter I} {f : I → D →ₗ[ℂ] D →ₗ[ℂ] ℂ}
    {g : D →ₗ[ℂ] D →ₗ[ℂ] ℂ} (hf : ∀ p q, Tendsto (fun i=> f i p q) l (𝓝 (g p q)))
    {p q:I→D}{v w}(hp:Tendsto p l (𝓝 v))(hq:Tendsto q l (𝓝 w)) :
    Tendsto (fun i => f i (p i) (q i)) l (𝓝 (g v w)) := by
    let A i:= (f i (p i)); apply Dash.arcing (W:=fun i=> (A i).toContinuousLinearMap)
       (X:=LinearMap.toContinuousLinearMap (g v)) (?_) hq
    refine Dash.fit_plane A (g v) (fun b=>?_); exact Dash.arcing (Dash.fit_plane
      (fun i=> LinearMap.comp (LinearMap.applyₗ (R:=ℂ) b) (f i)) (LinearMap.comp (LinearMap.applyₗ (R:=ℂ) b) g)
      (fun x=>hf x b)) hp

lemma free_limits {I : Type*} {l : Filter I} {p:I→D} {v} (hp:Tendsto p l (𝓝 v)) :
    Tendsto (fun i=> Levy.free2 (C:=C) d (p i) (reflect d (p i))) l (𝓝 (Levy.free2 (C:=C) d v (reflect d v))) :=
  varies d (g:=freeAt d C detectors) (f:=fun _=>freeAt d C detectors)
    (fun _ _=>tendsto_const_nhds) hp (reflect_limit d hp)
private def pullGram (r a : ℝ)(p : (Bel C.book).Field d) :=
    twoAt J d r (a • detectors) ((engine a) p) (reflect (C:=C) d ((engine a) p))
include H
private lemma limits {I : Type*} {l : Filter I} {r a:I→ℝ} (hr:Tendsto r l trail) {α:ℝ} (hα:0<α)
    (ha:Tendsto a l (𝓝 α)) {p:I→D} {v} (hp:Tendsto p l (𝓝 v)) :
    Tendsto (fun i=>pullGram d J (r i) (a i) (p i)) l (𝓝 (Levy.free2 (C:=C) d v (reflect d v))) := by
  have hx := Work.A05.smul_conf hα detectors_in
  let x:= α • detectors
  have he (u w:D) := leading_at F H (d:=fun _:Fin 2=>d) ![u,w] hr
     (ha.smul (tendsto_const_nhds (x:=detectors))) hx
  have ht:= Dash.arcing (Dash.fit_plane (fun i=> engine (a i)) (engine α)
    (fun v=> ((step_path d v).tendsto α).comp ha)) hp
  have hP:= varies d (g:=freeAt d C x) (f:=fun i=> twoAt J d (r i) (a i • detectors)) he ht (reflect_limit d ht)
  refine hP.mono_right (le_of_eq ?_)
  apply congr_arg
  change freeAt d C x ((engine α) v) (reflect d ((engine α) v))=_; rw [flip_dilation]
  refine Eq.trans ?_ (Pert.Scale.points_equ (F:=C.labels) detectors_in ![v,reflect d v] hα.ne')
  apply DFunLike.congr_arg ((Bel C.book).classMoment (Bel C.book) (fun _=>d) (α • detectors))
  exact funext fun i=> by fin_cases i<;> rfl
end coherent

private def sphere (d : ℕ) (C : Family G) := Metric.sphere (0:(Bel C.book).Field d) 1
private lemma free_bench : ∃ L U : ℝ, 0 < L ∧ 1 ≤ U ∧ ∀ p∈ sphere d C,
    L < ‖Levy.free2 (C:=C) d p (reflect d p)‖ ∧ ‖Levy.free2 (C:=C) d p (reflect d p)‖ < U := by
  let S' := sphere d C
  let v(p:D):= ‖Levy.free2 (C:=C) d p (reflect d p)‖
  have hc : IsCompact S' := isCompact_sphere ..
  have hv : Continuous v:= continuous_iff_continuousAt.mpr (fun x=> (free_limits d (v:=x) tendsto_id).norm)
  rcases S'.eq_empty_or_nonempty with hk|hk
  · exact ⟨1,1,one_pos,le_rfl,fun x hx=> (show x∈(∅:Set _) from (hk ▸ hx : x∈(∅:Set D))).elim⟩
  obtain ⟨x,hx,hmin⟩:= hc.exists_isMinOn hk hv.continuousOn
  obtain ⟨y,hy,hmax⟩:= hc.exists_isMaxOn hk hv.continuousOn
  have hz(p:D)(hp:p∈S'):0 < v p:= by
    apply norm_pos_iff.mpr (fun h=> ?_)
    have he : p ≠ 0 := fun hx=> by simp only [S',sphere,hx,Metric.mem_sphere,dist_self,zero_ne_one] at hp
    exact lt_irrefl (0:ℝ) ((Levy.free_positive d p he).trans_eq (congr_arg Complex.re h))
  refine ⟨v x/2,v y+1,half_pos (hz x hx),by have ht:= hz y hy; linarith only [ht],fun p hp=> ⟨(half_lt_self (hz x hx)).trans_le (hmin hp), (hmax hp).trans_lt (lt_add_one _)⟩⟩

private lemma reflect_smulC (t : ℝ) (u : D) : Levy.reflect d ((t:ℂ) • u) = (t:ℂ) • (Levy.reflect d u) := by
  unfold Levy.reflect; rw [LinearMap.map_smulₛₗ, Complex.conj_ofReal, map_smul]

private lemma gram_smul (r a b : ℝ) (u : D) (hb : 0 ≤ b) :
    ‖pullGram d J r a ((b:ℂ) • u)‖ = b^2 * ‖pullGram d J r a u‖ := by
  unfold pullGram; rw [map_smul,reflect_smulC,map_smul,map_smul, LinearMap.smul_apply]; rw [smul_smul,norm_smul,pow_two, ← Complex.ofReal_mul, Complex.norm_real,Real.norm_of_nonneg (by positivity)]

private lemma adjust_length {I : Type*} {l : Filter I} {a r : I→ℝ} {α : ℝ} (hα : 0<α)
    (ha : Tendsto a l (𝓝 α))(hr : Tendsto r l trail) : Tendsto (fun i=> a i*r i) l trail := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
  · convert ha.mul (hr.mono_right nhdsWithin_le_nhds) using 2; rw [mul_zero]
  filter_upwards [ha.eventually (lt_mem_nhds hα),hr.eventually (self_mem_nhdsWithin)] with i hi hu using mul_pos hi hu

private lemma compact_spheres (L U c : ℝ) (hc0 : 0<c) (h : ∀ v∈sphere d C,
    L < ‖Levy.free2 (C:=C) d v (reflect d v)‖ ∧ ‖Levy.free2 (C:=C) d v (reflect d v)‖ < U)
    (H : Leading F J) :
    let B r a v:= L ≤ ‖pullGram d J r a v‖ ∧ ‖pullGram d J r a v‖ ≤ U
    ∀ᶠ r in trail, ∀ t∈Icc c 1, ∀ p∈sphere d C, B r t p ∧ B (t*r) 1 p := by
  intro B; let V:= Icc c 1 ×ˢ sphere d C
  have ht : ∀ᶠ r in trail, ∀ v∈V, B r v.1 v.2 ∧ B (v.1*r) 1 v.2 := compact_event ℝ
    (isCompact_Icc.prod (isCompact_sphere ..)) (fun r v=> B r v.1 v.2 ∧ B (v.1*r) 1 v.2) (fun v hV=> ?_)
  exact ht.mono fun r hr t ht p hp=>hr (t,p) ⟨ht,hp⟩
  obtain ⟨h₁,h₂⟩:= h v.2 hV.2
  let u:= v.1
  have hu : 0 < u:= hc0.trans_le hV.1.1
  let l:= trail ×ˢ 𝓝 v
  have ha : Tendsto (fun z:ℝ × (ℝ × D)=> z.2.1) l (𝓝 u) := (tendsto_snd (f:=trail)).fst_nhds
  have hp : Tendsto (fun z:ℝ × (ℝ × D)=> z.2.2) l (𝓝 v.2) := (tendsto_snd (f:=trail)).snd_nhds
  have Q:=limits F d J H (α:=u) (p:=fun z:ℝ × (ℝ × D)=> z.2.2) tendsto_fst hu ha hp |>.norm
  have hq := (limits F d J H (adjust_length hu ha (r:=Prod.fst) tendsto_fst) one_pos tendsto_const_nhds hp).norm
  exact ((Q.eventually (le_mem_nhds h₁)).and (Q.eventually (ge_mem_nhds h₂))).and
             ((hq.eventually (le_mem_nhds h₁)).and (hq.eventually (ge_mem_nhds h₂)))

include H
private lemma two_sided : ∃ L U : ℝ, 0<L ∧ 1 ≤ U ∧ ∀ c:ℝ, 0 < c →
    let B r a p:= L * ‖p‖^2 ≤ ‖pullGram d J r a p‖ ∧ ‖pullGram d J r a p‖ ≤ U * ‖p‖^2
    ∀ᶠ r in trail, ∀ t∈Icc c 1, ∀ p:D, B r t p ∧ B (t*r) 1 p := by
  obtain ⟨L,U,hL,hU,H'⟩:= free_bench (C:=C) d
  refine ⟨L,U,hL,hU,fun c hc=>?_⟩
  intro B
  have ht (r a) (h : ∀ p∈sphere d C, L ≤ ‖pullGram d J r a p‖ ∧ ‖pullGram d J r a p‖ ≤ U)(p:D) :
      B r a p := by
    dsimp only [B]; by_cases he:p=0; subst p; simp [pullGram,reflect]
    let v:= ‖p‖; have hv:0<v:= norm_pos_iff.mpr he
    let q:D:= ((↑v⁻¹:ℂ)) • p
    have hq: (v:ℂ) • q=p:= by unfold q; push_cast; rw [smul_inv_smul₀]; exact_mod_cast hv.ne'
    have ht:q∈sphere d C:= by unfold q; rw [sphere, Metric.mem_sphere,dist_zero_right, norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]; exact inv_mul_cancel₀ hv.ne'
    rw [show ‖pullGram d J r a p‖=v^2*‖pullGram d J r a q‖ from (congrArg (fun z=>‖pullGram d J r a z‖) hq.symm).trans (gram_smul d J r a v q hv.le)]
    rw [mul_comm _ (‖pullGram ..‖)]
    exact ⟨mul_le_mul_of_nonneg_right (h q ht).1 (sq_nonneg _),mul_le_mul_of_nonneg_right (h q ht).2 (sq_nonneg _)⟩
  filter_upwards [compact_spheres F d J L U c hc H' H] with r hz t he p
  exact ⟨ht r t (fun x hx=> (hz t he x hx).1) p,ht (t*r) 1 (fun x hx=> (hz t he x hx).2) p⟩

omit H
/-- From measurement at λ r to frame at parent r, with reciprocal engineering factors (at the
    varying filter) already applied to the output of that comparison. -/
def cocycle (r a : ℝ) (h : 0 < a) :=
    ((J (a*r) d).trans (J r d).symm).trans (Pert.Scale.gearIso C.labels d a h).symm
private lemma at_one (u : D) : Pert.Scale.gear C.labels d 1 u=u:=by
   let B:= Extra.FD.recorded C.labels d
   rw [← B.b.sum_repr u,map_sum]; simp_rw [map_smul,Pert.Scale.rare]; simp
lemma cocycle_value (p:D)(t r : ℝ) (h : 0<t) : J r d ((engine t) (cocycle d J r t h p)) = J (t*r) d p:= by
   change J r d (Pert.Scale.gearIso C.labels d t h ((Pert.Scale.gearIso C.labels d t h).symm _)) = _
   rw [LinearEquiv.apply_symm_apply]; exact LinearEquiv.apply_symm_apply ..
private lemma two_transport (p:D)(t r : ℝ)(h : 0<t)(h₁ : Spin.realH F.room.kernel.spin (Free.spin_free C.labels) (J r d))
    (h₂ : Spin.realH F.room.kernel.spin (Free.spin_free C.labels) (J (t*r) d)) :
    pullGram d J (t*r) 1 p = pullGram d J r t (cocycle d J r t h p) := by
  rw [pullGram,pullGram,gram_at,gram_at,at_one,one_smul,cocycle_value,flip_coupled F d J r h₁,cocycle_value,flip_coupled F d J (t*r) h₂,smul_smul,mul_comm r t]

include H
theorem comparison : ∃ B : ℝ, 1 ≤ B ∧ ∀ c:ℝ, ∀ (hc:0<c),
    ∀ᶠ r in trail, ∀ t:ℝ, ∀ ht:t∈Icc c 1,
        let b := cocycle d J r t (hc.trans_le ht.1)
        (∀ p:D, ‖b p‖ ≤ B*‖p‖) ∧ ∀ p:D, ‖b.symm p‖ ≤ B*‖p‖ := by
  obtain ⟨L,U,hL,hU,h⟩:= two_sided F d J H
  let B:= Real.sqrt (U/L); have hu : 0≤ U/L := div_nonneg (zero_le_one.trans hU) hL.le
  have hX : 0 ≤ B:= Real.sqrt_nonneg _
  have hl (x y:D) (he : L * ‖x‖^2 ≤ U*‖y‖^2) : ‖x‖ ≤ max 1 B*‖y‖:= by
      suffices H : ‖x‖ ≤ B*‖y‖ from H.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
      refine le_of_sq_le_sq ?_ (mul_nonneg hX (norm_nonneg _)); rw [mul_pow,show B^2=_ from Real.sq_sqrt hu]; apply le_trans _ (le_of_eq (div_mul_eq_mul_div _ _ _).symm); exact (le_div_iff₀ hL).mpr ((mul_comm ..).trans_le he)
  obtain ⟨s,hs,hS⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp (H.equivariant d)
  refine ⟨max 1 B, le_max_left .., fun c hc=>?_⟩
  filter_upwards [show ∀ᶠ r in trail,r∈ Ioc 0 s from mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s,hs,subset_refl _⟩,h c hc] with r hr hP t ht
  have hh := hc.trans_le ht.1
  have he : t*r ∈ Ioc 0 s:=⟨mul_pos hh hr.1, (mul_le_of_le_one_left hr.1.le ht.2).trans hr.2⟩
  have hQ (p:D):= two_transport F d J p t r hh (hS hr) (hS he)
  intro b
  refine ⟨fun p=> hl _ _ ((hP t ht (b p)).1.1.trans ((congr_arg norm (hQ p).symm).trans_le (hP t ht p).2.2)),fun p=>?_⟩
  have hv : pullGram d J (t*r) 1 (b.symm p)=pullGram d J r t p := (hQ (b.symm p)).trans (congr_arg _ (b.apply_symm_apply p))
  exact hl _ _ ((hP t ht (b.symm p)).2.1.trans ((congr_arg norm hv).trans_le (hP t ht p).1.2))
end YM.PhysMS.Frame
