import YM.Trace.Fock.HighCap
/-! Fixed-scale pushforward of massless on-shell coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open YM Boundary Set Function Filter Complex MeasureTheory Measure
open scoped Topology BigOperators ENNReal Pointwise
variable {t : ℝ} {n : ℕ}
lemma scaled_meas_emb {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [MulAction ℝ X] [ContinuousConstSMul ℝ X] (ht : t≠0) : MeasurableEmbedding (fun x:X=>t • x) := (Homeomorph.smulOfNeZero t ht).measurableEmbedding -- check #check
lemma ν_dilation (ht : 0<t) : Measure.map (fun x : Mom => t • x) ν = ENNReal.ofReal (t⁻¹^2) • ν := by
 let g (x:Mom) := t • x
 let ρ (x:Mom) := ENNReal.ofReal (scalarWeight x)
 have hg : Measurable g := by dsimp only [g]; fun_prop
 have hm : Measurable ρ := ENNReal.measurable_ofReal.comp scalar_meas
 have h1 (w:Mom) : ρ w = ENNReal.ofReal t * ρ (g w) := by
     dsimp only [ρ,g]; rw [← ENNReal.ofReal_mul ht.le]; congr 1; unfold scalarWeight; rw [norm_smul,Real.norm_of_nonneg ht.le]; field
 have hv : Measure.map g volume = ENNReal.ofReal (t⁻¹^3) • volume := (map_addHaar_smul (E:=Mom) volume ht.ne').trans (by simp [Mom, YM.Space3,YM.SpaceAxis,_root_.abs_of_nonneg (pow_pos ht 3).le]) -- ?? abs inverse
 ext s hs
 unfold ν; rw [Measure.map_apply (f:=g) hg hs, withDensity_apply _ (hg hs),Measure.smul_apply,smul_eq_mul, withDensity_apply _ hs]
 change (∫⁻ x:Mom in _, ρ x) = _
 calc _ = ENNReal.ofReal t * ∫⁻ x:Mom in g⁻¹' s, ρ (g x) := by
         conv_lhs => enter [2,x]; rw [h1]
         exact lintegral_const_mul (f:=ρ ∘ g) _ (hm.comp hg)
      _ = ENNReal.ofReal t * (∫⁻ x in s, ρ x∂Measure.map g volume) := by rw [setLIntegral_map hs hm hg]
      _ = _ := by
         rw [hv,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul ht.le]; dsimp [ρ]; rw [show (t * t⁻¹^3 : ℝ)=t⁻¹^2 by field] 
lemma dilation_cords (n : ℕ) (ht:0<t) : Measure.map (fun x:Cords n=>t • x) (νpow n) = ENNReal.ofReal (t⁻¹^(2*n)) • νpow n := by
   unfold νpow
   haveI : SigmaFinite (Measure.map (fun x:Mom => t • x) ν) := (scaled_meas_emb ht.ne').sigmaFinite_map
   have hg := Measure.pi_map_pi (f:=fun _:Fin n=>fun (x:Mom)=> t • x) (μ:=fun _=>ν) (fun _=>by fun_prop)
   refine hg.trans (Measure.pi_eq (μ:=fun _ : Fin n=> _) ?_)
   intro s hs
   change (_•_ : Measure (Cords n)) (Set.univ.pi s)= _
   rw [Measure.smul_apply,smul_eq_mul, Measure.pi_pi]; simp_rw [ν_dilation ht, Measure.smul_apply, smul_eq_mul]
   rw [Finset.prod_mul_distrib, Finset.prod_const]; rw [Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity),pow_mul]; -- incorrect
lemma dilation_ae (ht : 0<t) : QuasiMeasurePreserving (fun x:Cords n => t • x) (νpow n) (νpow n) where
    measurable := (scaled_meas_emb ht.ne').measurable
    absolutelyContinuous := dilation_cords n ht|>.symm ▸ (smul_absolutelyContinuous (μ:=νpow n))
lemma energy_smul (t : ℝ) (x:Cords n): energy (t • x)=|t| * energy x := by unfold energy; simp [Pi.smul_apply, norm_smul, Finset.mul_sum]
lemma total_smul (ht : 0<t) (x:Cords n) : total (t • x)= t • total x := by unfold total; rw [Finset.smul_sum]; congr! 2 with i; exact Mink.ext_by (by simp) (by rw [ray_time, Pi.smul_apply, norm_smul,Real.norm_of_nonneg ht.le]; simp)
lemma region_smul (ht : 0<t) (x:Cords n) : (t • x)∈below n t ↔ x∈below n 1 := by rw [below]; change energy _ ≤ t ↔ energy _ ≤ 1; rw [energy_smul,_root_.abs_of_nonneg ht.le]; exact mul_le_iff_le_one_right ht -- check name

lemma generic_exchange (f : Cords n→ℝ) (ht:0<t) : (∫ x:Cords n, f (t • x) ∂νpow n) = (t⁻¹^(2*n))*∫ x, f x∂νpow n := by
   have hm (n): MeasurePreserving (fun x:Cords n=> t • x) _ _ := ⟨(scaled_meas_emb ht.ne').measurable,dilation_cords n ht⟩
   rw [(hm n).integral_comp (scaled_meas_emb ht.ne') f,integral_smul_measure,ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma region_exchange (f : Cords n→ℝ) (ht : 0<t) : (∫ x:Cords n in below n 1, f (t • x) ∂νpow n) = (t⁻¹^(2*n))*∫ x in below n t, f x∂νpow n := by
   have hh : (below n 1).indicator (fun x=>f (t • x))=fun x=>(below n t).indicator f (t • x) := funext (fun x=> by by_cases h:x∈below n 1 <;> simp_all [region_smul ht,Set.indicator])
   rw [← integral_indicator (below_meas _ 1), hh,← integral_indicator (below_meas _ t), generic_exchange _ ht]
end YM.Trace.Shell
