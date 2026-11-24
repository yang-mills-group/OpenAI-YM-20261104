import YM.AllOrder.Leading.Profile
import YM.OPE.Levy.Panel

/-!
# All-length Gram estimate for an aligned frame of any finite horizon

Does not invoke phase or all-order assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.FrameCost
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Leading Next.UVStress Maxwell Spin Push.FiniteDetection.Free OPE
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {n : ℕ} {d e : ℕ}
local notation "free" => Bel C.book
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

section ratios
/-- Convenience using log inverse length line. -/
def length (t : ℝ) := Real.exp (-t)
lemma positive (t : ℝ) : 0 < FrameCost.length t := Real.exp_pos _
lemma shrinking : Tendsto FrameCost.length atTop trail :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot,
       Eventually.of_forall FrameCost.positive⟩
lemma antitone : Antitone FrameCost.length := fun _ _ h=> Real.exp_monotone (neg_le_neg h)
lemma overshoot (t x : ℝ) : FrameCost.length (t+x) * Real.exp x= FrameCost.length t := by
    unfold FrameCost.length; rw [← Real.exp_add]; congr 1; ring
end ratios

lemma compact_zero (hU : Aligned F g U) (v : Fin n → (free).Tag) {ε : ℝ} (he : 0<ε)
      {K : Set (Points n)} (hK : IsCompact K) (hV : K ⊆ conf n) :
    ∀ᶠ r in trail, ∀ x ∈ K, ‖tableRead (U r) r v x-disc v x‖<ε := by
    filter_upwards [hU.jets n v 0 K hK hV he] with r hr x hx
    change ‖(tableRead (U r) r v-disc v) x‖<ε
    rw [←norm_iteratedFDeriv_zero (𝕜:=ℝ), show iteratedFDeriv ℝ 0 (tableRead (U r) r v-disc v) x= iteratedFDeriv ℝ 0 (tableRead (U r) r v) x-iteratedFDeriv ℝ 0 (disc v) x from ContinuousMultilinearMap.ext fun _=>rfl]
    exact hr x hx

/-- Scanner at standard symmetric reflected point, or any configured pair. -/
def reader (d : ℕ) (X : Spin.change S d) (r : ℝ) (x : Points 2) : E d →ₗ[ℂ] E d →ₗ[ℂ] ℂ where
    toFun v := (((Levy.linear₂ (S.classMoment S (fun _ : Fin 2=>d) (r • x))).comp X.toLinearMap) v).comp X.toLinearMap
    map_add' a b:=by rw [map_add]; rfl
    map_smul' c a:=by rw [map_smul]; rfl
abbrev leave (d:ℕ) (X:FamilyFrame S) (r : ℝ) := reader d (X d) r detectors
lemma readers (X : FamilyFrame S) (u v:E d) (r : ℝ) (x : Points 2) :
    reader d (X d) r x u v= tableRead X r (fun i:Fin 2 => (⟨d,![u,v] i⟩ : (free).Tag)) x := by
    change S.classMoment S _ _ _= S.classMoment S _ _ _
    refine DFunLike.congr_arg _ ?_; funext i; fin_cases i <;> rfl
variable (d) (h : Aligned F g U)
include h
lemma leaves_tend (u v : E d) : Tendsto (fun r => leave d (U r) r u v) trail (𝓝 (Levy.target (C:=C) d u v)) := by
    refine Metric.tendsto_nhds.mpr fun ε he=> ?_
    let p := fun i:Fin 2=> (⟨d,![u,v] i⟩ : (free).Tag)
    filter_upwards [compact_zero h p he isCompact_singleton (singleton_subset_iff.mpr detectors_in)] with r hr
    rw [dist_eq_norm]; change ‖reader d (U r d) r detectors u v - _‖ < _; rw [readers]; exact hr detectors rfl


omit h in
lemma tendsto2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {I : Type*} {l : Filter I} {x y : I→V} {x₀ y₀ : V} (B : I→V→ₗ[ℂ] V→ₗ[ℂ]ℂ) (C : V→ₗ[ℂ] V→ₗ[ℂ]ℂ)
    (h : ∀ u v, Tendsto (fun i=>B i u v) l (𝓝 (C u v)))
    (hx:Tendsto x l (𝓝 x₀))(hy:Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i=> B i (x i) (y i)) l (𝓝 (C x₀ y₀)) := by
    refine YM.Dash.arcing (W:=fun i=> (B i (x i)).toContinuousLinearMap)
       (X:=LinearMap.toContinuousLinearMap (C x₀)) ?_ hy
    refine YM.Dash.fit_plane _ _ fun p : V=> ?_
    let A := (LinearMap.applyₗ (R:=ℂ) p : (V →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ)
    exact YM.Dash.arcing (YM.Dash.fit_plane (fun i => A.comp (B i)) (A.comp C)
       (fun u => h u p)) hx
set_option maxHeartbeats 200000 in
lemma leaves_joint {I : Type*} {l : Filter I} {r : I → ℝ} {x y : I→ E d} {x₀ y₀ : E d}
    (hr:Tendsto r l trail)(hx:Tendsto x l (𝓝 x₀))(hy:Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => leave d (U (r i)) (r i) (x i) (y i)) l (𝓝 (Levy.target (C:=C) d x₀ y₀)) :=
    tendsto2 (fun i=> leave d (U (r i)) (r i)) (Levy.target (C:=C) d)
       (fun u v => (leaves_tend d h u v).comp hr) hx hy

-- Adaptation of Levy.norm_unit to all log lengths
private lemma floor_pair : ∃ c:ℝ,0<c ∧ ∀ᶠ t in (atTop : Filter ℝ),
    ∀ p:E d, ‖p‖=1 → c ≤ ‖leave d (U (FrameCost.length t)) (FrameCost.length t) p (Levy.reflect (C:=C) d p)‖ := by
    let x(t:ℝ) := FrameCost.length t
    let c (i:ℕ) : ℝ := 1/(i+1)
    by_contra! hf
    have hx (i : ℕ): ∃ t ≥ (i:ℝ), ∃ p:E d,‖p‖=1 ∧ ‖leave d (U (x t)) (x t) p (Levy.reflect (C:=C) d p)‖ < c i :=
      frequently_atTop.mp (hf (c i) (div_pos zero_lt_one (by positivity))) i
    choose t hT p hp hP using hx
    have ht:Tendsto t atTop atTop:=tendsto_atTop_mono hT tendsto_natCast_atTop_atTop
    obtain ⟨y,-,q,hq,hy⟩:=IsCompact.tendsto_subseq (isCompact_closedBall (0:E d) 1) (x:=p) (fun i=>mem_closedBall_zero_iff.mpr (by exact (hp i).le))
    have hpos:0<‖Levy.target (C:=C) d y (Levy.reflect d y)‖:=by
        have h1:=tendsto_nhds_unique hy.norm (tendsto_const_nhds.congr (fun i=> (hp (q i)).symm) : Tendsto (fun i=> ‖(p ∘ q) i‖) atTop (𝓝 1))
        have hy:y ≠ 0:= norm_ne_zero_iff.mp (h1.trans_ne one_ne_zero)
        rw [norm_pos_iff]; exact fun H => (Levy.free_positive d y hy).ne' (congr_arg Complex.re H)
    apply hpos.not_ge; let X:=x∘t∘q
    exact le_of_tendsto_of_tendsto' ((leaves_joint d h (FrameCost.shrinking.comp (ht.comp hq.tendsto_atTop))
       hy (Levy.reflect_limit d hy)).norm) (tendsto_one_div_add_atTop_nhds_zero_nat.comp hq.tendsto_atTop) (fun i=>(hP _).le)

omit h in
lemma reflects_real (p : E d) (a : ℝ) : Levy.reflect d ((a:ℂ) • p)=(a:ℂ) • Levy.reflect d p := by
    unfold Levy.reflect; rw [LinearMap.map_smulₛₗ]; simp
omit h in
lemma quadratic (X : E d →ₗ[ℂ] E d →ₗ[ℂ] ℂ) (p : E d) (a : ℝ) : X ((a:ℂ) • p) (Levy.reflect (C:=C) d ((a:ℂ) • p))= ((a:ℂ)^2) * X p (Levy.reflect d p):=by
    rw [reflects_real,map_smul,map_smul,LinearMap.smul_apply]; simp only [smul_eq_mul,pow_two,mul_assoc]
lemma coercive : ∃ c : ℝ, 0<c ∧ ∀ᶠ t in (atTop : Filter ℝ), ∀ p:E d,
    ‖p‖^2 ≤ c * ‖leave d (U (FrameCost.length t)) (FrameCost.length t) p (Levy.reflect (C:=C) d p)‖ := by
    obtain ⟨c,hc,hV⟩ := floor_pair d h
    refine ⟨c⁻¹,inv_pos.mpr hc,hV.mono fun i hi p => ?_⟩
    rcases eq_or_ne p 0 with rfl|hp
    · simpa only [norm_zero, zero_pow (show 2≠0 from by decide)] using mul_nonneg (inv_pos.mpr hc).le (norm_nonneg _)
    let X := leave d (U (FrameCost.length i)) (FrameCost.length i)
    let z:= ‖p‖⁻¹; have hz:0<z:= inv_pos.mpr (norm_pos_iff.mpr hp)
    have he:z*‖p‖=1:=inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)
    have h₁ : ‖(↑z:ℂ)‖=z:= (Complex.norm_real ..).trans (Real.norm_of_nonneg hz.le)
    have ht := hi ((z:ℂ) • p) (by rw [norm_smul,h₁,he]); rw [quadratic d,norm_mul,Complex.norm_pow,h₁] at ht
    apply (le_inv_mul_iff₀ hc).2
    calc _ ≤ z^2 * ‖X p (Levy.reflect d p)‖ * ‖p‖^2:=mul_le_mul_of_nonneg_right ht (sq_nonneg _)
         _ = _:=by change ‖p‖⁻¹^2 * _ * _ = _; field_simp [(norm_ne_zero_iff.mpr hp)]; rfl
end YM.AllOrder.FrameCost
