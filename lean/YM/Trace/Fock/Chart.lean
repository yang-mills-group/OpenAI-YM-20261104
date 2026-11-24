import YM.Trace.Fock.Tables
noncomputable section
set_option maxHeartbeats 400000
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter MeasureTheory Function Set YM Boundary Complex
open scoped ENNReal Pointwise Topology BigOperators
variable {n m : ℕ}
def limitedTest (K : ℕ) (s : Set Mom) (hs : MeasurableSet s) : filterRapid where
 val := (s ∩ Metric.closedBall 0 K).indicator (fun _=>1)
 property := ⟨measurable_const.indicator (hs.inter Metric.isClosed_closedBall.measurableSet),fun k=>by
     classical
     refine ⟨(1+(K:ℝ))^k,by positivity,fun p=> ?_⟩
     by_cases h : p ∈ s ∩ Metric.closedBall (0:Mom) K
     · rw [Set.indicator_of_mem h,norm_one,← div_eq_mul_inv,one_le_div (weight_pos ..)]; dsimp only [weight]; exact pow_le_pow_left₀ (by positivity) (by exact add_le_add_right (by simpa using! h.2) _) _
     simp only [indicator_of_notMem h,norm_zero]; unfold weight; positivity⟩
abbrev generalBox (n : ℕ) (K : ℕ) := univ.pi (fun _:Fin n => Metric.closedBall (0:Mom) K)
lemma measurable_generalBox : MeasurableSet (generalBox n m) := MeasurableSet.pi (to_countable _) (fun _ _=> Metric.isClosed_closedBall.measurableSet)
lemma limited_mask (K : ℕ) (s : Fin n→Set Mom) (hs : ∀ i, MeasurableSet (s i)) (x) : testJoint (fun i=> limitedTest K (s i) (hs i)) x= ((univ.pi s)∩generalBox n K).indicator (fun _=>1) x := by
 classical
 unfold testJoint limitedTest; dsimp only
 by_cases h : x∈ univ.pi s ∩ generalBox n K; · rw [indicator_of_mem h]; exact Finset.prod_eq_one (fun b _=> indicator_of_mem  (s:=_ ∩ _) ⟨h.1 b (mem_univ _),h.2 b (mem_univ _)⟩ (fun _=>1))
 have hh : ∃ i:Fin n, x i ∉ s i ∩ Metric.closedBall 0 K := by contrapose h; push_neg at h; exact ⟨fun i _=>(h i).1,fun i _=>(h i).2⟩
 obtain ⟨i,hi⟩:=hh
 rw [indicator_of_notMem h]; exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)

variable (v : Test4→L[ℂ] Sum m) (hv : FieldImage v) (k : @Angle m (n+1))
private lemma integrable_boxes (F : Cords n→ℂ) (K : ℕ) (he : ∀ w, Integrable (fun x=> F x * testJoint w x) (νpow _)) : IntegrableOn F (generalBox n K) (νpow n) := by
    rw [← integrable_indicator_iff measurable_generalBox]; exact (he (fun i=>limitedTest K univ MeasurableSet.univ)).congr (.of_forall fun x=> by
        dsimp only; rw [limited_mask K (fun _ : Fin n=>univ) (fun _=>MeasurableSet.univ)]; by_cases h:x∈generalBox n K <;> simp [Set.indicator,h,pi_univ])
private lemma limit_chart {q} (P : chartIdx q n → ℂ) (F : Cords n → ℂ) (he : ∀ w, Integrable (fun x=> F x * testJoint w x) (νpow n)) (hP : ∀ w, Integrable (fun x=> chartValue P x*testJoint w x) (νpow n)) (ha : ∀ w, (∫ p, F p * testJoint w p∂νpow n)=∫ p, chartValue P p*testJoint w p∂νpow n) : F=ᶠ[ae (νpow n)] chartValue P := by
   let μ := νpow n
   have hQ (F:Cords n→ℂ) u (s : Fin n→Set Mom) (hs : ∀ i, MeasurableSet (s i)) : ∫ x in (univ.pi s∩generalBox n u), F x∂μ = ∫x, (F:Cords n→ℂ) x * testJoint (fun i=>limitedTest u (s i) (hs i)) x ∂μ := by
         rw [← integral_indicator (s:=univ.pi _∩_) ((MeasurableSet.pi (to_countable _) (fun i _=> hs i)).inter measurable_generalBox)] -- check
         exact integral_congr_ae (.of_forall fun x=> by dsimp only; rw [limited_mask u s hs]; by_cases h:x∈univ.pi s ∩ generalBox _ u <;> simp [Set.indicator,h])
   have hh (u : ℕ) : IntegrableOn F (generalBox n u) μ := integrable_boxes F u he
   have hPK u := integrable_boxes _ u hP
   have H (u : ℕ) (s : Fin n→Set Mom) (hs : ∀ i, MeasurableSet (s i)) : ∫ x in (univ.pi s), (F x - chartValue P x) ∂μ.restrict (generalBox n u) = 0 := by
       rw [Measure.restrict_restrict (by exact MeasurableSet.pi (to_countable _) (fun i _=>hs i)), MeasureTheory.integral_sub ((hh _).mono_set (inter_subset_right)) ((hPK _).mono_set inter_subset_right), hQ F u s hs, hQ (chartValue P) u s hs]
       exact sub_eq_zero.mpr (ha _)
   have hz (u : ℕ) : let g := F-chartValue P
                     Integrable g (μ.restrict (generalBox n u)) ∧ ∀ s : Set (Cords n), MeasurableSet s → ∫ p in s, g p∂μ.restrict (generalBox n u)=0 := by
      let g := F - chartValue P
      refine ⟨(hh u).sub (hPK ..),?_⟩; have hFI : Integrable g (μ.restrict (generalBox n u)) := (hh u).sub (hPK ..)
      refine MeasurableSpace.induction_on_inter generateFrom_pi.symm isPiSystem_pi (by simp) ?_ ?_ ?_ -- proof motives in Prop
      · intro t ⟨s,hs,hst⟩; refine hst ▸ H u s (fun i=> hs i (mem_univ _))
      · intro t ht h; have htot := H u (fun i: Fin n => univ) (fun _=> MeasurableSet.univ)
        rw [setIntegral_compl ht hFI, h,sub_zero]; simpa [μ,g] using! htot
      intro s h hs H
      rw [integral_iUnion hs h hFI.integrableOn];
      exact Eq.trans (tsum_congr (fun j => H j)) (by simp)
   have Hx (u:ℕ) : ∀ᵐ p ∂μ, p∈generalBox n u → F p=chartValue P p := (ae_restrict_iff' measurable_generalBox).mp (((hz u).1.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _=> (hz u).2 s hs)).mono fun p hx=> sub_eq_zero.mp hx)
   filter_upwards [ae_all_iff.mpr Hx] with p hp
   obtain ⟨l,hl⟩:=exists_nat_ge ‖p‖
   exact hp l (fun i _=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (norm_le_pi_norm p i).trans hl))

include hv
lemma shell_chart : ∃ q : ℕ, ∃ c : chartIdx q (n+1) → ℂ, smoothBody v k=ᶠ[ae (νpow (n+1))] chartValue c := by
 obtain ⟨q,c,hc⟩:=chartEvidence v hv k
 exact ⟨q,c, limit_chart c _ (joint_integrable v k hv) (fun w=>chart_testable v hv w c) hc⟩
end YM.Trace.Shell
