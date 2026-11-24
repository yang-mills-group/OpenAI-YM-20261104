import YM.SharpGram.Load.Spin
/-! Uniform convergence of true relative rotations on entire group. Use
already established generator convergence + *fixed representation for all k*. Haar
in normalization in `Align`. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Extraction Org NormedSpace Spec
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
set_option quotPrecheck false
local notation "E" => Maxwell.Free.gear C.labels
local notation "T" => F.phase.transport
local notation "S'" => Bel C.book
local notation "α" => F.sector.turns
section span
-- `μ` uniform circumriction from fixed finite-dimensional coefficient space.
variable {X Y Z:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][NormedAddCommGroup Y][NormedSpace ℂ Y][FiniteDimensional ℂ X][FiniteDimensional ℂ Y]
theorem spine (B:Z→X)(T0:ℕ→X→ₗ[ℂ] Y) (h:∀ i,Tendsto (fun k=> T0 k (B i)) atTop (𝓝 0)) {ε: ℝ}(he:0<ε) : ∀ᶠ k:ℕ in atTop, ∀ i, ‖T0 k (B i)‖ ≤ ε*‖B i‖ := by
    let Q := Submodule.span ℂ (range B); let L(k) := LinearMap.toContinuousLinearMap ((T0 k).comp Q.subtype)
    have hu : Tendsto L atTop (𝓝 0) := by
      apply Dash.fit_plane (fun k=> (L k).toLinearMap) (0 : Q→ₗ[ℂ] Y)
      intro x; let W (v:X) := Tendsto (fun k=> T0 k v) atTop (𝓝 0)
      change W x.val
      apply Submodule.span_induction (p:=fun z _=>W z) _ _ _ _ x.property
      · exact fun i ⟨x,e⟩=> e ▸ h x
      · simp [W]
      · intro i j _ _ hi hj; unfold W; simp_rw [map_add]; rw [← add_zero (0:Y)]; exact hi.add hj
      intro c i _ hi; unfold W; simp_rw [map_smul]; rw [← smul_zero c]; exact tendsto_const_nhds.smul hi
    filter_upwards [(Metric.tendsto_nhds (a:=(0:Q→L[ℂ] Y)) (u:=L)).mp hu ε he] with k hk i
    let x:Q:= ⟨B i,Submodule.subset_span (mem_range_self _)⟩
    have hy : dist (L k) 0<ε:= hk
    have hy : ‖L k‖<ε:=(dist_zero_right (L k)) ▸ hy
    exact (ContinuousLinearMap.le_opNorm (L k) x).trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))
end span
variable {u : Filter (ℕ×ℕ)}
variable (B : Lenses.Mantle F u)
section
variable (d:ℕ)
def renders {L:Register G}{S:Table L}(A:S.Rotation)(v:Ortho) : Spin.Mat (S.Field d) :=
   LinearMap.toContinuousLinearMap (A.act d v).toLinearMap
lemma renders_sends {L:Register G}{S:Table L}{K:S.Rotation}{P:DiffPlan S}{H:S.RealSpin} (h:K.Laws P H)(v w:Ortho):renders d K (v*w)=renders d K v * renders d K w:=ContinuousLinearMap.ext (fun x=> h.group d v w x)
lemma renders_start {L:Register G}{S:Table L}{K:S.Rotation}{P:DiffPlan S}{H:S.RealSpin}(h:K.Laws P H): renders d K 1=1:=ContinuousLinearMap.ext (fun x=> h.fixes d x)
lemma renders_live {L:Register G}{S:Table L}{K:S.Rotation}{P:DiffPlan S}{H:S.RealSpin}(h:K.Laws P H): Continuous (renders d K):= continuous_iff_continuousAt.mpr fun g => Dash.fit_plane (fun t:Ortho => (K.act d t).toLinearMap) (K.act d g).toLinearMap fun x => (h.spin d x).continuousAt.tendsto
lemma model_renders {C:Family G}(g:Ortho) : model C d g=renders d (Maxwell.Free.gear C.labels) g:= rfl
lemma repl (k:ℕ)(g:Ortho)(x:(Bel C.book).Field d) : act B k d g x=(B.lens k d).symm ((α).act d g (B.lens k d x)):=rfl
lemma repl_prod (k:ℕ)(v w:Ortho) : act B k d (v*w)=act B k d v * act B k d w := by
   refine ContinuousLinearMap.ext fun x => ?_; change _ = act B k d v (act B k d w x)
   simp_rw [repl,(T).spots.group,LinearEquiv.apply_symm_apply]
lemma repl_start (k:ℕ) : act B k d 1=1:= ContinuousLinearMap.ext fun x=> by rw [repl,(T).spots.fixes,LinearEquiv.symm_apply_apply];rfl

variable (hg:OPE.Services C f S)
include hg
-- needs compatibility only with current witness.
lemma group (g:Ortho) : Tendsto (fun k=> act B k d g) atTop (𝓝 (renders d E g)):= by
   let hX := (T).spots; let hY := Maxwell.Free.gear_laws C.labels
   let P(g:Ortho):= Tendsto (fun k=> act B k d g) atTop (𝓝 (renders d E g))
   have he:P 1:= by unfold P; rw [renders_start d hY]; simp_rw [repl_start]; exact tendsto_const_nhds
   have hm (v w: Ortho) (hv:P v)(hw:P w): P (v*w):= by
      unfold P; simp_rw [repl_prod]; rw [renders_sends d hY]; exact hv.mul hw
   let L:Subgroup Ortho:=
     { carrier := {i | P i ∧ P i⁻¹}
       one_mem' := And.intro he (show P _ by rw [inv_one]; exact he)
       mul_mem' {v w} hv hw := And.intro (hm v w (show P v ∧ P v⁻¹ from hv).1 (show P w ∧ P w⁻¹ from hw).1) ((mul_inv_rev v w).symm ▸ hm _ _ hw.2 hv.2)
       inv_mem' {v} hv := And.intro (show P v ∧ P v⁻¹ from hv).2 (by rw [inv_inv]; exact hv.1) }
   have he (s: Signed):P s.ortho:= by
      unfold P; apply tendsto_const_nhds.congr'; filter_upwards [B.aged d] with k hk
      apply ContinuousLinearMap.ext;intro x
      rw [repl,hX.signed]; let Y:=B.lens k d; let w:= E; have hv := (hk.1 _ le_rfl).1 s x
      change (E).act d s.ortho x= _
      rw [hY.signed]; apply (B.lens k d).injective; rw [(B.lens k d).apply_symm_apply]; exact hv
   have ht:Bid.AxisGens ≤ L := by
      apply (Subgroup.closure_le L).mpr
      rintro j (⟨s,rfl⟩|⟨v,t,rfl⟩)
      · exact And.intro (he s) ((show s⁻¹.ortho=s.ortho⁻¹ from map_inv Signed.inclusionO _ ) ▸ he s⁻¹)
      have hh : Ortho.oneParameter v (-t)=(Ortho.oneParameter v t)⁻¹ := by
          apply mul_right_cancel (b:=Ortho.oneParameter v t) -- check syntax
          rw [← add_parameter,neg_add_cancel,parameter_start,inv_mul_cancel]
      exact ⟨spinsAt B hg _ _, hh ▸ (spinsAt B hg (d:=d) v (-t))⟩
   exact (show P g ∧ P g⁻¹ from ht ((show Bid.AxisGens=⊤ from Work.A13.answer).symm ▸ Subgroup.mem_top g)).1

def pulled (k d:ℕ): Spin.Mat (S.Field d) →ₗ[ℂ] Spin.Mat ((Bel C.book).Field d) where
   toFun g := LinearMap.toContinuousLinearMap ((B.lens k d).symm.toLinearMap.comp (g.toLinearMap.comp (B.lens k d).toLinearMap))
   map_add' x y := ContinuousLinearMap.ext (fun v => (B.lens k d).symm.map_add (x (B.lens k d v)) (y (B.lens k d v)))
   map_smul' c x := ContinuousLinearMap.ext (fun v => (B.lens k d).symm.map_smul c (x (B.lens k d v)))

attribute [local instance] YM.Work.A15.compact_ortho
lemma entirely (ε:ℝ)(he:0<ε) : ∀ᶠ k in atTop, ∀ v:Ortho, ‖act B k d v - renders d E v‖ ≤ ε := by
   let w (v:Ortho):= (renders d α v,renders d E v)
   let X:=Spin.Mat (S.Field d); let Y:=Spin.Mat ((Bel C.book).Field d)
   let f(k) : X×Y →ₗ[ℂ] Y := (pulled B k d).comp (LinearMap.fst ℂ X Y) - LinearMap.snd ..
   have h(v:Ortho): Tendsto (fun k=>f k (w v)) atTop (𝓝 0) := by
      change Tendsto (fun k=> act B k d v - renders d E v) atTop (𝓝 0)
      simpa only [sub_self] using ((group B d hg v).sub_const (renders d E v))
   obtain ⟨C,hC⟩ := (isCompact_range (f:= fun i=> ‖w i‖) (Continuous.norm ((renders_live d (T).spots).prodMk (renders_live d (Maxwell.Free.gear_laws C.labels))))).bddAbove
   let c:ℝ:=max 1 C;have hc:0<c:=zero_lt_one.trans_le (le_max_left ..)
   filter_upwards [spine w f h (div_pos he hc)] with k hk v
   exact (hk v).trans ((mul_le_mul_of_nonneg_left ((hC (mem_range_self _)).trans (le_max_right ..)) (div_nonneg he.le hc.le)).trans_eq (div_mul_cancel₀ ε hc.ne'))
end
end YM.SharpGram.Load
