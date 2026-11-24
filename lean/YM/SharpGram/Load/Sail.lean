import YM.SharpGram.Load.Uniform
import YM.OPE.Orbits.Average

/-!
# Produce an orthogonally aligned window basis without perturb prerequisites

Same physical field and free comparators. Carry filtration and unit by
linear average. Projection/filter prices transferred with bounded constants,
*no* rate here promising beyond leading. Does not imply that other
perturbatively calculated frames admit such bounded near-identity transforms.
Uses full true-rotation convergence. Public package in sequel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Extraction Analysis Org Spec MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
set_option quotPrecheck false
local notation "E" => Maxwell.Free.gear C.labels
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "T" => F.phase.transport
local notation "S'" => Bel C.book
local notation "α" => F.sector.turns
local notation "V" => F.sector.derivatives
local notation "V'" => Maxwell.Free.scheme C.labels
local notation "σ"=> F.room.kernel.spin

section halo
-- Keep Measure instances consistent with OPE prescription
attribute [local instance] OPE.Orbits.measO OPE.Orbits.borelO YM.Work.A15.compact_ortho
local instance : SecondCountableTopology Ortho := by
    haveI:SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology (Axis→Axis→ℝ))
    exact inferInstanceAs (SecondCountableTopology ↥(Matrix.unitaryGroup Axis ℝ : Set M4))
local notation "μ" => OPE.Orbits.haar
local instance : OPE.Orbits.haar.IsHaarMeasure := by unfold OPE.Orbits.haar; infer_instance
local instance : IsProbabilityMeasure μ := by unfold OPE.Orbits.haar; exact ⟨Measure.haarMeasure_self⟩
local instance {G:Gauge}{L:Register G}(S:Table L)(d:ℕ): FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _
-- norm conversion
private lemma insulating {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (x:X)
    (q:ℕ→Ortho→X) (hq:∀ i,Integrable (q i) μ) (h:∀ ε:ℝ,0<ε → ∀ᶠ i:ℕ in atTop, ∀ k, ‖q i k-x‖ ≤ ε) :
     Tendsto (fun i=>∫ v,q i v ∂μ) atTop (𝓝 x):=by
    apply Metric.tendsto_nhds.mpr; intro ε hε
    filter_upwards [h (ε/2) (half_pos hε)] with k hk
    rw [dist_eq_norm]; have ht : ‖∫ v,q k v - x ∂μ‖ ≤ ε/2 * Measure.real μ univ := norm_integral_le_of_norm_le_const (Eventually.of_forall hk)
    rw [integral_sub (hq k) (integrable_const x)] at ht
    exact le_trans (show _ ≤ ε/2 from (by simpa using ht)) le_rfl|>.trans_lt (half_lt_self hε)

variable {u : Filter (ℕ×ℕ)} (B : Lenses.Mantle F u)
local notation "A" => B.lens
-- input to the physical Mantle: changes the free labels BEFORE leaf switch
private def cargo (k d:ℕ)(v:Ortho):= act B k d v * renders d E v⁻¹
private lemma cargo_int (k d:ℕ): Integrable (cargo B k d) μ := by
   apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
   let P := pulled B k d
   have hc : Continuous ((P : Spin.Mat (S.Field d) →ₗ[ℂ] _)):= P.continuous_of_finiteDimensional
   exact (hc.comp (renders_live d (T).spots)).mul ((renders_live d (Maxwell.Free.gear_laws C.labels)).comp continuous_inv)

def shift (k d:ℕ): Spin.Mat ((Bel C.book).Field d) := ∫ v,cargo B k d v ∂μ
lemma sails (hg: OPE.Services C f S) (d:ℕ): Tendsto (fun k=>shift B k d) atTop (𝓝 1):= by
    obtain ⟨a,ha⟩:= (isCompact_range (f:=fun i=> ‖renders d E i‖) (renders_live d (Maxwell.Free.gear_laws C.labels)).norm).bddAbove
    let c:ℝ:= max a 1; have hx:0<c:=zero_lt_one.trans_le (le_max_right ..)
    refine insulating 1 (fun k=> cargo B k d) (fun _=>cargo_int ..) (fun ε he=> ?_)
    filter_upwards [entirely B d hg (ε/c) (div_pos he hx)] with k hk g
    let Z:= Maxwell.Free.gear_laws C.labels
    have ht : cargo B k d g - 1=(act B k d g -renders d E g)*renders d E g⁻¹ := by
        rw [sub_mul,← renders_sends d Z,mul_inv_cancel,renders_start d Z]; rfl
    rw [ht]; exact (norm_mul_le ..).trans ((mul_le_mul (hk _) ((ha (mem_range_self _)).trans (le_max_left ..)) (norm_nonneg _) (div_nonneg he.le hx.le)).trans_eq (div_mul_cancel₀ ε hx.ne'))

private lemma cargo_comm (k d:ℕ)(v w:Ortho) :
    cargo B k d (v*w) * renders d E v=act B k d v * cargo B k d w:= by
   unfold cargo; rw [← mul_assoc,repl_prod] -- orient fix
   let Z:=Maxwell.Free.gear_laws C.labels
   rw [mul_assoc,← renders_sends d Z,show (v*w)⁻¹*v=w⁻¹ from by group,mul_assoc]
lemma shift_comm (k d:ℕ) (v:Ortho) :
    shift B k d * renders d E v=act B k d v * shift B k d:= by
   unfold shift
   let X:=Spin.Mat ((Bel C.book).Field d); let R := renders d E
   let P : X→L[ℝ] X := ((ContinuousLinearMap.mul ℂ X).flip (R v)).restrictScalars ℝ
   let Q : X→L[ℝ] X := (ContinuousLinearMap.mul ℂ X (act B k d v)).restrictScalars ℝ
   change P (∫ w,cargo B k d w ∂μ) = Q (∫ w,cargo B k d w ∂μ)
   have hs:=cargo_int B k d; rw [← P.integral_comp_comm hs,← Q.integral_comp_comm hs]
   rw [← (measurePreserving_mul_left μ v).integral_comp (g:=fun w => P (cargo B k d w)) (Homeomorph.mulLeft v).measurableEmbedding]
   exact integral_congr_ae (Eventually.of_forall fun w=> cargo_comm B k d v w)

private def starOp (d:ℕ) (C:Family G) : realHom (Bel C.book) (Bel C.book) d := LinearMap.toContinuousLinearMap {
    toFun := (Bel C.book).conj (Maxwell.Free.spin_free C.labels) d
    map_add' := map_add _
    map_smul' r x := by
      change Table.conj _ _ _ (r • x)=r • Table.conj _ _ _ x
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smulₛₗ]; simp }

lemma shift_real (d:ℕ) : ∀ᶠ k in atTop, ∀ x, shift B k d ((S').conj θ d x)= (S').conj θ d (shift B k d x):= by
   let P:= starOp d C
   filter_upwards [B.aged d] with k hk x
   let X:=A k d; let R:=act B k d
   have hX (x : (S').Field d): X (P x)= S.conj σ d (X x):= (hk.1 d le_rfl).2.1 x
   have hA (w:Ortho)(x:(S').Field d): R w (P x)= P (R w x):= X.injective (by
      rw [hX]; unfold R; simp_rw [repl]; change X (X.symm ((α).act d w (X (P x))))= S.conj σ d (X (X.symm _)); rw [hX,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,(T).spots.real] )
   let L := ContinuousLinearMap.apply ℂ ((Bel C.book).Field d) x
   let u := (ContinuousLinearMap.apply ℂ ((Bel C.book).Field d) (P x)).restrictScalars ℝ
   let v := P.comp (L.restrictScalars ℝ)
   have hs:=cargo_int B k d
   change u (∫ j,cargo B k d j ∂μ) = v (∫ j,cargo B k d j ∂μ)
   rw [← u.integral_comp_comm hs,← v.integral_comp_comm hs]
   apply integral_congr_ae; filter_upwards with g
   change R g ((E).act d g⁻¹ (P x))= P (R g ((E).act d g⁻¹ x))
   rw [show (E).act d g⁻¹ (P x) = P ((E).act d g⁻¹ x) from (Maxwell.Free.gear_laws C.labels).real .. |>.symm]; exact hA g _
lemma shift_fixes (d:ℕ) : ∀ᶠ k in atTop, shift B k d ((S').unit d)=(S').unit d:=by
   let W:=(S').unit d
   filter_upwards [B.aged d] with k hk
   have he g : cargo B k d g W=W := by
     change act B k d g ((E).act d g⁻¹ ((S').unit d))= W
     rw [repl]; let Y:=A k d
     rw [(Maxwell.Free.gear_laws C.labels).identity]; apply Y.injective
     rw [show Y ((S').unit d)=_ from (hk.1 d le_rfl).2.2]
     rw [(T).spots.identity]; exact LinearEquiv.apply_symm_apply Y _
   let Q := (ContinuousLinearMap.apply ℂ ((Bel C.book).Field d) W).restrictScalars ℝ
   change Q (∫ g,cargo B k d g ∂μ) = W
   rw [← Q.integral_comp_comm (cargo_int B k d)]; simp_rw [show ∀ g:Ortho,Q (cargo B k d g)=W from he]; simp

lemma shift_filtered {d e:ℕ} (hd:d≤e) : ∀ᶠ k in atTop, ∀ x, shift B k e ((V').rise hd x)= (V').rise hd (shift B k d x) := by
   let Q:=(V').rise hd
   filter_upwards [B.aged e] with k hk x
   have hY(v): A k e (Q v)= (V).rise hd (A k d v):= hk.2 _ _ hd le_rfl v
   have hx(g)(v): act B k e g (Q v)= Q (act B k d g v):= (A k e).injective (by rw [hY]; unfold act; change A k e ((A k e).symm ((α).act e g (A k e (Q v)))) = (V).rise hd (A k d ((A k d).symm _)); rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hY,(T).spots.filtered]; rfl)
   have he g: cargo B k e g (Q x)=Q (cargo B k d g x):=by
     change act B k e g ((E).act e g⁻¹ ((V').rise hd x))= _
     rw [(Maxwell.Free.gear_laws C.labels).filtered]; exact hx ..
   let L := (ContinuousLinearMap.apply ℂ ((Bel C.book).Field e) (Q x)).restrictScalars ℝ
   let M := ((LinearMap.toContinuousLinearMap Q).comp (ContinuousLinearMap.apply ℂ ((Bel C.book).Field d) x)).restrictScalars ℝ
   change L (∫ g,cargo B k e g ∂μ) = M (∫ g,cargo B k d g ∂μ)
   rw [← L.integral_comp_comm (cargo_int B k e),← M.integral_comp_comm (cargo_int B k d)]; exact integral_congr_ae (Eventually.of_forall he)

end halo
end YM.SharpGram.Load
