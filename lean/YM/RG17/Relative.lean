import YM.RG17.Decode
import YM.Extra.MULTISOURCE_TRAJECTORIES.Smooth

/-!
# Joint profile in actual continuum measurement

Cluster in r-scaled Euclidean lengths relative to external center (integrated).
In constructing absolute test of n+k points from it, retain translation and
Jacobian even through the lattice adapter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Filter Set Function MeasureTheory Extraction TopologicalSpace WithLp Table OPE OPE.Orbits
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {S:Table C.book} {n k:ℕ}

private def pad2 : WithLp 2 (Points n × Points k) ≃ₗᵢ[ℝ] Points (n+k) where
    toFun q:= points (Fin.append q.fst.ofLp q.snd.ofLp)
    invFun p:= toLp 2 (points (fun i=> p (Fin.castAdd k i)), points fun i=> p (Fin.natAdd n i))
    left_inv p:=by apply ofLp_injective 2; apply Prod.ext <;> (apply PiLp.ext; intro i; simp)
    right_inv p:=by apply PiLp.ext; intro i; cases i using Fin.addCases <;> simp
    map_add' p q:=by apply PiLp.ext; intro i; cases i using Fin.addCases <;> simp
    map_smul' c p:=by apply PiLp.ext; intro i; cases i using Fin.addCases <;> simp
    norm_map' p:=by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
        rw [WithLp.prod_norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2 _ p.fst,PiLp.norm_sq_eq_of_L2 _ p.snd,Fin.sum_univ_add]; simp

def pad : (Points n × Points k) ≃L[ℝ] Points (n+k) := (prodContinuousLinearEquiv 2 ℝ (Points n) (Points k)).symm.trans pad2.toContinuousLinearEquiv
theorem pad_volume : MeasurePreserving (pad (n:=n) (k:=k)):=by
    change MeasurePreserving (pad2 (n:=n) (k:=k) ∘ toLp 2) volume volume
    exact MeasurePreserving.comp (pad2 (n:=n) (k:=k)).measurePreserving (WithLp.volume_preserving_toLp _ _)
theorem pad_xy (x: Points n × Points k) : pad x=points (Fin.append x.1.ofLp x.2.ofLp) := rfl

def openRoot : (E4 × Points k) ≃L[ℝ] Points (k+1) := (prodContinuousLinearEquiv 2 ℝ E4 (Points k)).symm.trans Points.peel.symm.toContinuousLinearEquiv
theorem openRoot_volume : MeasurePreserving (openRoot (k:=k)):=by
    change MeasurePreserving ((Points.peel (n:=k)).symm ∘ toLp 2) volume volume
    exact MeasurePreserving.comp (Points.peel (n:=k)).symm.measurePreserving (WithLp.volume_preserving_toLp _ _)
theorem openRoot_eq (o:E4)(y:Points k) : openRoot (o,y)= Points.cons o y :=rfl

private def copyEcho (n:ℕ): E4→ₗ[ℝ] Points n := ⟨⟨fun s=> points fun _=>s,fun _ _=>rfl⟩,fun _ _=>rfl⟩

def echo (n:ℕ): E4→L[ℝ] Points n := ⟨copyEcho n, (by
    change Continuous (fun x:E4=> toLp 2 (fun _ : Fin n=>x))
    fun_prop)⟩
lemma echo_at (u:E4)(i:Fin n): (echo n u).ofLp i=u := rfl

/-- offset x included in poses, then translated with external z at center. -/
def absCord (n k:ℕ)(r:ℝ) (p : Points n × Points (k+1)) : Points (n+k) :=
   pad (r•p.1 + echo n ((openRoot.symm p.2).1), (openRoot.symm p.2).2)
set_option maxHeartbeats 300000 in
lemma absCord_cont (r:ℝ):Continuous (absCord n k r):=by
   unfold absCord
   have h0 : Continuous (fun x: Points n × Points (k+1)=> r • x.1) :=by fun_prop
   have h1 : Continuous (fun x: Points n × Points (k+1)=> openRoot.symm x.2) :=by
       apply Continuous.comp (g:= (openRoot (k:=k)).symm) (f:=Prod.snd) (openRoot (k:=k)).symm.continuous continuous_snd -- done
   -- continuous_snd
   have h2 : Continuous (fun x: Points n × Points (k+1)=> echo n ((openRoot.symm x.2).1)) :=by
       exact Continuous.comp (g:= echo n) (echo n).continuous h1.fst
   exact (pad (n:=n) (k:=k)).continuous.comp ((h0.add h2).prodMk h1.snd)

variable (X:External C S)

/-- Absolute test leg; Jacobian with respect to cluster length only. -/
def absolute (X:External C S)(r:ℝ)(ψ:Test n)(x:Points (n+X.n)) :ℂ:=
   (r:ℂ)⁻¹ ^ (4*n) * ∫ u:E4, X.test (openRoot (u,((pad (n:=n)).symm x).2)) *
       ψ (r⁻¹ • (((pad (n:=n)).symm x).1 - echo n u))

set_option maxHeartbeats 300000 in
lemma absolute_smooth (r:ℝ)(ψ:Test n): ContDiff ℝ ∞ (absolute X r ψ):=by
   let P:= pad (n:=n) (k:=X.n)
   let V:= openRoot (k:=X.n)
   let Z (p: Points (n+X.n) × E4) :ℂ:= X.test (V (p.2,(P.symm p.1).2))*ψ (r⁻¹ • ((P.symm p.1).1-echo n p.2))
   let K: Set E4:= (Prod.fst ∘ V.symm) '' (tsupport X.test)
   have h: IsCompact K := X.test.hasCompactSupport.image (continuous_fst.comp V.symm.continuous)
   let μ:= (volume:Measure E4).comap ((↑):K→E4)
   haveI : IsFiniteMeasure μ:=by
      constructor; change (Measure.comap _ _) _ < _; rw [(MeasurableEmbedding.subtype_coe h.measurableSet).comap_apply,image_univ,Subtype.range_coe]; exact h.measure_lt_top
   have he (x:Points (n+X.n)):(∫ p:K,Z (x,p) ∂μ) = ∫ u:E4,Z (x,u):=by
      apply (integral_subtype_comap h.measurableSet (fun u:E4=>Z (x,u))).trans; apply setIntegral_eq_integral_of_forall_compl_eq_zero; intro u hu
      have hx: (V (u,(P.symm x).2)) ∉ tsupport X.test:= fun h=>hu ⟨_,h,by simp only [comp_apply,ContinuousLinearEquiv.symm_apply_apply]⟩
      simp [Z,image_eq_zero_of_notMem_tsupport hx]
   have h1: ContDiff ℝ ∞ (fun p: Points (n+X.n) × E4 => P.symm p.1):= P.symm.contDiff.comp contDiff_fst
   have h2: ContDiff ℝ ∞ (fun p: Points (n+X.n) × E4 => echo n p.2):=by
       exact ContDiff.comp (g:= echo n) (f:=Prod.snd) (echo n).contDiff contDiff_snd
   have h3: ContDiff ℝ ∞ (fun p: Points (n+X.n) × E4 => r⁻¹ • ((P.symm p.1).1 - echo n p.2)) := ((contDiff_fst.comp h1).sub h2).const_smul r⁻¹
   have h4: ContDiff ℝ ∞ (fun p: Points (n+X.n) × E4 => V (p.2,(P.symm p.1).2)) := V.contDiff.comp (contDiff_snd.prodMk (contDiff_snd.comp h1))
   have hz: ContDiff ℝ ∞ Z := (X.test.contDiff.comp h4).mul (ψ.contDiff.comp h3)
   have hv:=Extra.Trajectories.integral_smooth (p:=((↑):K→E4)) (μ:=μ) continuous_subtype_val.aestronglyMeasurable h (fun i:K=>i.2) hz
   simp_rw [he] at hv; exact contDiff_const.mul hv
lemma absolute_lands {K:Set (Points n)} (hk:IsCompact K) {ψ:Test n}(hp:tsupport ψ⊆K) {r:ℝ}(hr:r≠0) : tsupport (absolute X r ψ) ⊆
     absCord n X.n r '' (K ×ˢ tsupport X.test):=by
   apply closure_minimal _ (((hk.prod X.test.hasCompactSupport).image (absCord_cont _)).isClosed); intro y hy
   contrapose! hy
   apply notMem_support.mpr; unfold absolute; rw [integral_eq_zero_of_ae, mul_zero]; filter_upwards with u
   let v:= (pad (n:=n)).symm y; let x:=r⁻¹ • (v.1-echo n u); let z:= openRoot (u,v.2)
   change X.test z * ψ x=0; by_cases h:z∈tsupport X.test; swap
   · simp [image_eq_zero_of_notMem_tsupport h]
   have hA:x ∉ tsupport ψ:= by
       intro he; apply hy; exact ⟨(x,z),⟨hp he,h⟩,by unfold absCord; simp [z,x,hr,v]⟩
   simp [image_eq_zero_of_notMem_tsupport hA]

lemma pad_separates (x:Points n)(y:Points k): Injective (beside x.ofLp y.ofLp) ↔ pad (x,y)∈conf _:=by
    let M:=beside x.ofLp y.ofLp
    let e : Fin n ⊕ Fin k ≃ Fin (n+k):= finSumFinEquiv
    let W:= (pad (x,y)).ofLp
    change Injective M ↔ Injective W
    have hx:W ∘ e=M:=by
        funext i; cases i <;> simp [W,M,e, beside,pad_xy, Function.comp]
    rw [← hx]; constructor
    · intro h; have he:W=(W ∘ e) ∘ e.symm:=funext fun i=> (congr_arg W (e.apply_symm_apply i)).symm
      rw [he]; exact h.comp e.symm.injective
    exact fun h=>h.comp e.injective

lemma rooted_packing (r:ℝ)(x:Points n)(z:Points (X.n+1)):
     Injective (beside (posed r x) (X.offset z)) ↔ absCord n X.n r (x,z) ∈ conf (n+X.n) := by
    obtain ⟨⟨u,v⟩,rfl⟩:= openRoot.surjective z
    simp only [absCord,ContinuousLinearEquiv.symm_apply_apply]
    rw [← pad_separates]
    have he:beside (r•x+ echo n u).ofLp v.ofLp=(fun i=>i+u)∘ (beside (posed r x) (X.offset (openRoot (u,v)))) :=by
       funext i; cases i <;> simp [echo_at,posed, External.offset,openRoot_eq,Points.cons,comp] -- adjust
    rw [he]; exact ⟨fun h=> (add_left_injective u).comp h, fun h=>h.of_comp⟩

variable {f:Extraction.Order}{F:Spec.Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S)
def packs (X: External C S) (r:ℝ)(ψ:Test n) : Prop:=
   absCord n X.n r '' (tsupport ψ ×ˢ tsupport X.test) ⊆ conf _

include H P
lemma roomFor {K:Set (Points n)}(hk:IsCompact K)(hx:K ⊆ conf n):∀ᶠ r in home,
     absCord n X.n r '' (K ×ˢ tsupport X.test) ⊆ conf _ := by
    obtain ⟨T,η,hT,hη,hp⟩:=roomCosts hk hx
    obtain ⟨δ,hδ,hz⟩:= X.range_open
    let v:= (0:Labels S (fun _:Fin n=>0))
    filter_upwards [positiveLength,profile_scope (ε:=1) F P H v X.labels hT hη hδ one_pos 0] with r hr hv x hx
    obtain ⟨⟨x,z⟩,he,rfl⟩:= hx
    exact (rooted_packing X r x z).mp ((hv.2 ((posed r x,0,X.offset z):Loc (Fin n) (Fin X.n)) ⟨hp r hr _ he.1,hz _ he.2⟩).1.2.1)

omit H P

def shape (X:External C S)(r:ℝ)(ψ:Test n) : Test (n+X.n):=
   if h:r≠0 ∧ packs X r ψ then ⟨absolute X r ψ,absolute_smooth ..,
     (((ψ.hasCompactSupport.prod X.test.hasCompactSupport).image (absCord_cont r)).of_isClosed_subset isClosed_closure (absolute_lands X ψ.hasCompactSupport subset_rfl h.1)),
     (absolute_lands X ψ.hasCompactSupport subset_rfl h.1).trans h.2⟩ else 0
lemma shaped {r:ℝ}(hr:r≠0){ψ:Test n}(hp:packs X r ψ): ⇑(shape X r ψ)=absolute X r ψ :=by
   unfold shape; rw [dif_pos ⟨hr,hp⟩]; rfl
end YM.RG17
