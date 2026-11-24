import YM.RG17.Probe

/-!
# Exterior bounds from a tested signed discrepancy

`Services` gives the spatial estimate for the selected prescription on
smooth probes at positive clearance. Does NOT supply the corresponding
estimate for the RG report; it requires an actual returned vector with
(replication/source) control of *these* tested discrepancies on unselected
S. Pay the finite collection on SAME input/output. Gives all-probes
minimum requirements; the output report may depend on that finite list.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (L:Layout F)
variable {n:ℕ} {d:Fin n→ℕ}

-- If using a reactor with only product tests in absolute coordinates,
-- one must justify (all) this relative testing on the same report.
def appeared (F:Final C f S)(v:Labels S d)(X:External C S)(r:ℝ)(ψ:Test n):ℂ :=
    ∫ z:Points (X.n+1), X.test z * query F v (X.offset z) X.labels none r ψ

variable (h:Services C f S)
include h P
set_option maxHeartbeats 400000 in
lemma appearedIntegrable {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)(X:External C S):
    ∀ᶠ r in home,∀ v:Labels S d,∀ ψ:Test n,tsupport ψ⊆K→
      Integrable (fun z:Points (X.n+1)=> X.test z * query F v (X.offset z) X.labels none r ψ) := by
   obtain ⟨T,η,hT,hη,hs⟩:= roomCosts hK hx
   obtain ⟨δ,hδ,hx⟩:= X.range_open
   filter_upwards [positiveLength, profile_scope (ε:=1) F P h (0:Labels S d) X.labels hT hη hδ one_pos 0] with r hr h' v ψ hψ
   let A y x:= X.test y * (ψ x* whole S (posed r x) v (X.offset y) X.labels)
   let K':Set (Points (X.n+1) × Points n):= tsupport X.test ×ˢ tsupport ψ
   have hP(q:Points (X.n+1) × Points n)(h:q∉ K'): uncurry A q=0:=by
       change X.test q.1 * _= _
       by_cases hp:q.1∈tsupport X.test
       · have hh:q.2∉ tsupport ψ:= fun hv=> h ⟨hp,hv⟩
         simp [image_eq_zero_of_notMem_tsupport hh]
       simp [image_eq_zero_of_notMem_tsupport hp]
   have hy:IsCompact K':= X.test.hasCompactSupport.prod ψ.hasCompactSupport
   have hM: HasCompactSupport (uncurry A) := hy.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx=>by
       by_contra h; exact hx (hP x h)) hy.isClosed)
   have hB:Continuous (uncurry A):=by
       refine continuous_iff_continuousAt.mpr fun z=> ?_
       by_cases h:z∈ K'
       · let C' (q:Points (X.n+1) × Points n):Loc (Fin n) (Fin X.n):=(posed r q.2,0,X.offset q.1)
         have he: C' z∈ guardZone F P 0:= (h'.2 (C' z) ⟨hs _ hr _ (hψ h.2),hx _ h.1⟩).1
         refine ((X.test.continuous.comp continuous_fst).continuousAt).mul (g:=(fun z:Points (X.n+1) × Points n=> ψ z.2 * whole S (posed r z.2) v (X.offset z.1) X.labels)) ?_
         exact ((ψ.continuous.comp continuous_snd).continuousAt).mul ((whole_cont_at v X.labels _ F.room.kernel he.2.1).comp (f:=C')
           (((posed_continuous r).comp continuous_snd|>.prodMk (continuous_const.prodMk (X.continuous_offset.comp continuous_fst))).continuousAt))
       refine ContinuousAt.congr (f:=fun _ : Points (X.n+1) × Points n=> (0:ℂ)) continuousAt_const
        ((show ∀ᶠ x in 𝓝 z,x ∉ K' from hy.isClosed.isOpen_compl.mem_nhds (show z∈ K'ᶜ from h)).mono fun x hx=> (hP x hx).symm)
   have hv : Integrable (uncurry A) (volume.prod volume):= hB.integrable_of_hasCompactSupport hM
   have hz(y:Points (X.n+1)):(∫ x:Points n,A y x)= X.test y * query F v (X.offset y) X.labels none r ψ:=by unfold A; rw [integral_const_mul]; rfl
   exact hv.integral_prod_left.congr (Eventually.of_forall fun z=> hz z)

include L
lemma exteriorBound (hL:Located L) (X:External C S)(slots:(i:Fin n)→Slot C (d i)) (D:ℕ) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n) {ε:ℝ}(hε:0<ε) :
    ∀ᶠ r in home,∀ ψ:Test n,tsupport ψ⊆ K → ‖appeared F (stems L slots r) X r ψ-
        X.charge F D (basket P D (stems L slots r) r ψ)‖ ≤
      r^((D+1:ℝ)-ε)*(∫ x:Points (X.n+1), ‖X.test x‖) * (∫ x:Points n, ‖ψ x‖):=by
    obtain ⟨δ,hδ,hv⟩:= X.range_open
    let a := (D+1:ℝ)-ε
    filter_upwards [positiveLength,testedPacketLocated P L h hL slots D hK hx hε hδ X.labels,
      appearedIntegrable (d:=d) P h hK hx X] with r hr hx hp ψ hψ
    let V:=stems L slots r
    let z:=basket P D V r ψ
    change ‖(∫ i:Points (X.n+1), X.test i * query F V (X.offset i) X.labels none r ψ)- ∫ i:Points _, X.test i*X.pay D z i‖≤ _
    rw [← MeasureTheory.integral_sub (hp V ψ hψ) (X.pay_integrable F D z)]
    refine (norm_integral_le_of_norm_le (g:=fun i:Points (X.n+1)=> ‖X.test i‖*(r^a*(∫ x:Points n, ‖ψ x‖))) ?_ ?_).trans_eq ?_
    · exact (X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport|>.norm).mul_const _
    · filter_upwards with i
      by_cases hb:i∈tsupport X.test; swap
      · have hc:X.test i=0:= image_eq_zero_of_notMem_tsupport hb; simp [hc]
      rw [← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (hx ψ hψ (X.offset i) (hv _ hb) none) (norm_nonneg _)
    rw [integral_mul_const]; ring -- unfold a

omit L h P
structure TestedOutput {F:Final C f S} (L:Layout F) {d:Fin n→ℕ}(slots:(i:Fin n)→Slot C (d i))(D:ℕ) (W:Finset (External C S))
    (K:Set (Points n)) (M:Test n → ℝ → C.label D) : Prop where
   spatial : ∃ (b:ℝ) (C₀:ℝ) (j:ℕ), 0<b ∧ 0≤C₀ ∧ ∀ᶠ r in home,
     ∀ X∈ W,∀ ψ:Test n,tsupport ψ⊆ K→ ∀ A:ℝ,Demand j ψ A →
       ‖appeared F (stems L slots r) X r ψ - X.charge F D (master L D r (M ψ r))‖ ≤ C₀*r^((D:ℝ)+b)*A
include P L h
set_option maxHeartbeats 400000 in
/-- Ordinary coefficient discrepancy (in physical label norm BEFORE inverting
scaling). Conditional only on actual tested comparison of the signed product
vs reported single column, at real support/derivative costs there.
Use the SAME M later when pricing perturbative remainder. -/
lemma spatialLocated (loc:Located L)(slots:(i:Fin n)→Slot C (d i))(D:ℕ) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n):
   ∃ W:Finset (External C S), ∀ M:Test n→ℝ→C.label D, TestedOutput L slots D W K M →
    ∃ (b:ℝ) (C₀:ℝ) (j:ℕ), 0<b ∧ 0≤C₀ ∧ ∀ᶠ r in home,
     ∀ ψ:Test n,tsupport ψ⊆ K→ ∀ A:ℝ,Demand j ψ A →
       ‖basket P D (stems L slots r) r ψ - master L D r (M ψ r)‖ ≤ C₀*r^((D:ℝ)+b)*A := by
   obtain ⟨W,c,hc,hW⟩:= finiteProbes F D
   refine ⟨W,fun M hM=>?_⟩
   obtain ⟨b,C₀,j,hb,h₀,H⟩:= hM.spatial
   let q :ℝ:=min b (1/2)
   let f (X:External C S):ℝ:= ∫ x:Points (X.n+1), ‖X.test x‖
   have hf (X:External C S):0≤f X:=integral_nonneg fun _=>norm_nonneg _
   refine ⟨q,c*(∑ X∈W,(f X+C₀)),j,lt_min hb (by norm_num),mul_nonneg hc (Finset.sum_nonneg fun i _=>add_nonneg (hf _) h₀),?_⟩
   filter_upwards [positiveLength,H,(show ∀ᶠ r in home,r ≤ (1:ℝ) from nhdsWithin_le_nhds (ge_mem_nhds zero_lt_one)),
     ((eventually_all_finset W).mpr (fun (i:External C S) _=> exteriorBound (ε:=1/2) P L h loc i slots D hK hx (by norm_num)))]
     with r hr hh hr' hQ ψ hψ A hA
   let X':= basket P D (stems L slots r) r ψ
   let Y':= master L D r (M ψ r)
   let B:= r ^ ((D:ℝ)+q)
   have hP(X:External C S)(hw:X∈W): ‖X.charge F D (X'-Y')‖ ≤(f X+C₀)*(B*A):=by
       let T := appeared F (stems L slots r) X r ψ
       let U:= X.charge F D
       rw [map_sub]
       apply le_trans (norm_sub_le_norm_sub_add_norm_sub (U X') T (U Y'))
       rw [norm_sub_rev,add_mul]; refine add_le_add ?_ ?_
       · apply le_trans (hQ X hw ψ hψ); rw [mul_left_comm,← mul_assoc]; refine mul_le_mul ?_ hA.norm (integral_nonneg fun _=>norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hr.le _) (hf X)); apply mul_le_mul_of_nonneg_right ?_ (hf X); exact Real.rpow_le_rpow_of_exponent_ge hr hr' (by linarith only [min_le_right b (1/2:ℝ)])
       apply le_trans (hh X hw ψ hψ A hA); rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ h₀) hA.nonneg; exact Real.rpow_le_rpow_of_exponent_ge hr hr' (add_le_add_right (min_le_left b _) _)
   refine (hW _).trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum hP) hc).trans_eq ?_)
   rw [← Finset.sum_mul]; dsimp only [B]; ring
end YM.RG17

