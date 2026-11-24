import YM.MatchingR2.Top.Slice

/-! Test the integrated law against the covariant read, not the result of keeping just
one minimization branch. Restore the actual denominator & push for use with inserted fields.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set Tree Push.SectorMeasure
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (β : ℝ) (o : Site c)
set_option quotPrecheck false
local notation "Fine" => Config G f
local notation "Coarse" => Config G c
abbrev Read := S.Choices → Fine → Coarse → ℝ
def pullRead (A : Read (G:=G) S) (x : All S F G) := A ((tag S).symm x.2.1) (F.drape x.2.2) (turned o x.1)
variable (H : S.patch.Branches S.kernel G) {A : Read (G:=G) S}
    (he : ∀ i, Envelope (uncurry (A i))) (hc : ∀ i, Covariant S (A i))
include he
lemma pulledReadBound : Envelope (pullRead S F o A) := by
  have hu : Measurable (fun p:All S F G => (F.drape p.2.2, turned o p.1)) := by
    refine (fullSlice_meas S F).prodMk ?_
    change Measurable (turned o ∘ Prod.fst)
    exact (turned_continuous o).measurable.comp measurable_fst
  have hm : Measurable (fun p:All S F G=>p.2.1) := measurable_fst.comp measurable_snd
  let f' (j : Key S) (x : All S F G) := uncurry (A ((tag S).symm j)) (F.drape x.2.2, turned o x.1)
  have ht (j : Key S) : Envelope (f' j) := envelope_comp (he _) hu
  let V := envelope_readTag hm (f:=f') ht
  exact V

include H hc
lemma cov_report (V : Coarse) : report S F β o (pullRead S F o A) V =
    (∑ i,∫ U : Fine, ticket S β i U V * A i U V ∂prior G f) / coarseWeight S β V := by
  rw [report,(bothLaw S F β o H).answer_id]; congr 1
  let Z (q : Key S) a := stamp S F β o (V,q,a)*pullRead S F o A (V,q,a)
  have hz := envelope_section _ ((stamp_env S F β o H).mul (pulledReadBound S F o he)) V
  change (∫ i, Z i.1 i.2 ∂base S F G)=_
  rw [open_base S F Z (show Envelope (uncurry Z) from hz)]
  exact Finset.sum_congr rfl fun i _=> by
    simp only [Z,stamp,pullRead,Equiv.symm_apply_apply]; exact cov_section S F β H i V o _ (he i) (hc i)
lemma cov_income : ∫ x, pullRead S F o A x ∂full S F β o G =
    ∑ i, ∫ U, (∫ V, ticket S β i U V * A i U V ∂prior G c) ∂prior G f := by

  let a := pullRead S F o A
  let g := coarseWeight S β (G:=G)
  let p := prior G f; let q := prior G c
  let w i V U := ticket S β i U V*A i U V
  have hw (i:S.Choices) : Integrable (uncurry (w i)) (q.prod p) := by
    have h₁ : Envelope (fun x : Coarse×Fine => ticket S β i x.2 x.1) := ticket_env S β H measurable_snd measurable_fst i
    exact ((h₁.mul (envelope_comp (he i) measurable_swap)).integrable (μ:=(prior G c).prod (prior G f)))
  calc
    _ = ∫ V, g V * report S F β o a V ∂prior G c := by
      rw [← fromWeight_integral q g (fun i=>(coarse_weight_pos S β H _).le)
        ((bothLaw S F β o H).payroll.meas)]
      exact ((bothLaw S F β o H).saves _ (pulledReadBound S F o he)).symm
    _ = ∫ V, (∑ i:S.Choices, ∫ U, w i V U ∂p) ∂q := by
      congr 1; ext1 V; unfold a; rw [cov_report S F β o H he hc]; unfold g p w; field_simp [(coarse_weight_pos S β H V).ne']
    _ = _ := by
      rw [integral_finsetSum (μ:=q) (f:=fun i V => ∫ U, w i V U ∂p) Finset.univ (fun (i:S.Choices) _=> (hw i).integral_prod_left)]
      exact Finset.sum_congr rfl fun i _=> integral_integral_swap (hw i)

omit he hc
-- Often take Z a plain stencil product with no coarse or tag costs on input.
theorem report_to_push (V : Coarse) {Z : Fine → ℝ} (hz : GaugeInvariant Z) (hZ : Envelope Z) :
    report S F β o (fun x => Z (F.drape x.2.2)) V =
      (S.push β (fun U => fineWeight β U * Z U) V) / coarseWeight S β V := by
  let a := fun (_:S.Choices) U (_:Coarse) => Z U
  have he := cov_report S F β o H (A:=a) (fun i=> envelope_comp hZ (measurable_fst (β:=Coarse)))
    (fun _ t U V=> hz t U) V
  refine he.trans ?_; congr 1
  unfold a StepData.push StepData.density; simp_rw [smul_eq_mul]
  rw [← integral_finsetSum (μ:=prior G f) Finset.univ (f:=fun i U=> ticket S β i U V * Z U)
    (fun i _=> ((ticket_env S β H (U:=id) measurable_id (V:=fun _=>V) measurable_const i).mul hZ).integrable _)]
  congr 1; ext1 U; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; unfold ticket tagged; ring

theorem original (Z : Fine → ℝ) (hz : GaugeInvariant Z) (hZ : Envelope Z) :
    ∫ x : All S F G, Z (F.drape x.2.2) ∂full S F β o G = ∫ U : Fine, Z U ∂law G f β := by
  let f' (x:All S F G) := Z (F.drape x.2.2)
  let w (U: Fine) := fineWeight β U * Z U
  let z := coarseWeight S β (G:=G)
  have ht : Envelope f' := envelope_comp hZ (fullSlice_meas S F)
  calc
    _ = ∫ V : Coarse, z V * report S F β o f' V ∂prior G c := by
      rw [← fromWeight_integral (prior G c) z (fun i=>(coarse_weight_pos S β H _).le)
        ((bothLaw S F β o H).payroll.meas)]; exact ((bothLaw S F β o H).saves f' ht).symm
    _ = ∫ V, S.push β w V ∂prior G c := by
      congr 1; ext1 V; unfold f'; rw [report_to_push S F β o H V hz hZ]; unfold z w; field_simp [(coarse_weight_pos S β H V).ne']
    _ = _ := by
      have hi : Envelope w := (fine_weight_env β).mul hZ
      rw [StepData.push_integral (S.isKernel H β) w (hi.integrable _)]
      exact (fromWeight_integral (prior G f) (fineWeight β) (fun i => (fine_weight_pos β _).le)
        (fine_weight_env β).meas Z).symm

-- although Schedule may admit more, formula wanted by assembly on its own reps.
omit H
lemma coarse_actual {β' : ℝ} {G : Gauge} (h : History G) (hh : h.Selected) (N q : ℕ)
    (hn : h.β (N+1) q (N+1)=β') (V : Config G (h.S.side N q)) : coarseWeight (h.levels.clock.op N q) β' V =
      (h.rep (N+1) q N).eval V / partition G (h.S.side (N+1) q) β' := by
  subst hn
  -- integrable so real
  rw [(hh.steps (N+1) q N (Nat.lt_succ_self _)).1,(hh.starts ..).2]; unfold coarseWeight StepData.push fineWeight; simp_rw [smul_eq_mul, mul_div_assoc']; rw [integral_div]
end YM.MatchingR2.Top
