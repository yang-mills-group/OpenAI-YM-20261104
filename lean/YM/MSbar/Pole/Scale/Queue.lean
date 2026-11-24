import YM.MSbar.Pole.Scale.Regular

/-! # Remainders of rays as dimensionally holomorphic symbols -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ray
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "ν" => volume.restrict (Ioc (0:ℝ) 1)
private def step (t:ℝ): ℂ × (ℝ × E)→L[ℝ] ℂ×(ℝ × E) :=
  let Q:= ContinuousLinearMap.snd ℝ ℂ (ℝ × E); (ContinuousLinearMap.fst ℝ ℂ _).prod
    ((t • ((ContinuousLinearMap.fst ℝ ℝ _).comp Q)).prod ((ContinuousLinearMap.snd ℝ ℝ _).comp Q))
@[simp] private lemma step_apply (z:ℂ) (t s : ℝ)(x:E):step t (z,s,x)=(z,t*s,x):=rfl

/-- Repeated real-variable expansion; by fiber so never requires a formula for
ζ outside the open holomorphy set. -/
def spill (F : ℂ→ ℝ × E→ℂ) (z : ℂ) (v : ℝ × E):= ∫ u:ℝ in Ioc (0:ℝ) 1, deriv (fun s : ℝ=>F z (s,v.2)) (u*v.1)
variable {F : ℂ→ ℝ × E→ℂ} {U:Set ℂ}
private def advance (F : ℂ→ℝ × E→ℂ) := fieldD ((0:ℂ),(1:ℝ),(0:E)) (fun p=>F p.1 p.2)

private lemma advanceAt (z : ℂ)(x:E)(t:ℝ)(h : DifferentiableAt ℝ (fun p:ℂ × (ℝ×E)=>F p.1 p.2) (z,t,x)) :
    HasDerivAt (fun t:ℝ=>F z (t,x)) (advance F (z,t,x)) t := by
  have ht := h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t z).prodMk ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))); exact ht

local notation "ρ" => ticket (@id (ℝ × E))

lemma more (o : IsOpen U) (h : Wall U ρ 1 F): Wall U ρ 1 (spill F) := by
  let v : ℂ × ℝ × E := (0,1,0)
  have he : Packet (strip (ℝ × E) U) (stretch ρ) 1 (advance F) := h.stream.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ v)
  have hv : Barrel ν (strip (ℝ × E) U) (stretch ρ) 1 (fun t x=> advance F (step t x)) := by
    let p:= stretch ρ
    have hb := pullBarrel step (p:=p) (q:=1) (μ:=ν) (T:=fun _ : ℝ=>0) he (o.prod isOpen_univ)
      (show ContinuousOn (fun x:ℂ × ℝ × E=>1+‖x.2‖) _ from continuousOn_const.add continuousOn_snd.norm) zero_le_one ?_ ?_ ?_
    · simpa only [zero_add] using hb
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; rintro ⟨z,s,x⟩
      rw [step_apply,one_mul]; have hu:‖t*s‖ ≤ ‖s‖:=by rw [norm_mul,Real.norm_of_nonneg ht.1.le]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      change max ‖z‖ (max ‖t*s‖ ‖x‖) ≤ max ‖z‖ (max ‖s‖ ‖x‖); gcongr
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
      rcases x with ⟨z,s,x⟩; simp only [step_apply,zero_add,one_mul]
      refine ⟨⟨hx.1,mem_univ _⟩,?_,le_rfl⟩
      change 1+max ‖t*s‖ ‖x‖ ≤ 1+max ‖s‖ ‖x‖
      have hu:‖t*s‖ ≤ ‖s‖:= by rw [norm_mul,Real.norm_of_nonneg ht.1.le]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      gcongr
    · rintro ⟨z,s,x⟩ hx; simp only [zero_add,step_apply]; apply Continuous.aestronglyMeasurable; refine continuous_iff_continuousAt.mpr fun t=>?_
      exact (he.smooth (z,t*s,x) ⟨hx.1,mem_univ _⟩).continuousAt.comp (x:=t) (f:=fun i:ℝ=>(z,i*s,x)) (by fun_prop)
  let Y (x:ℂ × ℝ × E):= ∫ t,advance F (step t x) ∂ν
  have hh (x:ℂ × ℝ × E) (hx : x ∈ strip (ℝ × E) U): (fun x:ℂ×ℝ×E=>spill F x.1 x.2) =ᶠ[𝓝 x] Y := by
    filter_upwards [(o.prod isOpen_univ).mem_nhds hx] with i hi
    rcases i with ⟨z,s,w⟩; unfold spill Y; congr 1; ext1 t; rw [(advanceAt z w (t*s) (h.stream.smooth (z,t*s,w) ⟨hi.1,mem_univ _⟩ |>.differentiableAt (by simp))).deriv]; rfl
  have hp := hv.integrates.congr hh; refine ⟨hp,fun z hz x=> (coordinates (U:=fun p:(ℂ × ℝ × E) => spill F p.1 p.2) ((hp.smooth _ ⟨hz,mem_univ x⟩).differentiableAt (by simp))).mp ?_⟩
  apply CR.germ _ (hh (z,x) ⟨hz,mem_univ x⟩)
  refine integral_cr hv ⟨hz,mem_univ x⟩ ?_
  rcases x with ⟨s,x⟩
  filter_upwards with u
  have ht : step u (z,s,x)∈strip (ℝ×E) U:=⟨hz,mem_univ _⟩
  have h':= field_cr (o.prod isOpen_univ) h.stream h.cr v ht
  refine CR.pull _ ((step (E:=E) u).hasFDerivAt) ((he.smooth _ ht).differentiableAt (by simp)) ?_
  have hr (w : ℂ) : step u (w,(0:ℝ × E))=(w,0) := by rw [Prod.zero_eq_mk]; simp only [step_apply,mul_zero]
  change CR (step u _) (step u _) _ _; rw [hr,hr]; exact h'

lemma terms (o : IsOpen U) (h : Wall U ρ 1 F) (k:ℕ): Wall U ρ 1 (spill^[k] F) := by induction k with
  | zero=> exact h
  | succ k ih=> rw [iterate_succ_apply']; exact more o ih
lemma splitAt (h : Wall U ρ 1 F) {z:ℂ} (hz:z∈U)(t:ℝ)(x:E) : F z (t,x)= F z (0,x)+(t:ℂ)*spill F z (t,x):=by
  have hs (v:ℝ):=advanceAt z x v ((h.stream.smooth (z,v,x) ⟨hz,mem_univ _⟩).differentiableAt (by simp))
  let g(v:ℝ):= F z (v*t,x); let B(u:ℝ):=advance F (z,u*t,x)
  have hg (u:ℝ): HasDerivAt g ((t:ℂ)* B u) u:=by
    rw [← Complex.real_smul]
    exact (hs _).scomp u (show HasDerivAt (fun u:ℝ=>u*t) t u by simpa using (hasDerivAt_id' u).mul_const t)
  let v : ℂ × (ℝ×E):=(0,1,0)
  have hB : Continuous B := continuous_iff_continuousAt.mpr fun u=> by exact ((h.stream.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ v)).smooth (z,u*t,x) ⟨hz,mem_univ _⟩).continuousAt.comp (f:=fun u:ℝ=> (z,u*t,x)) (x:=u) (by fun_prop)
  unfold spill; simp_rw [(hs _).deriv]; rw [← intervalIntegral.integral_of_le (f:=B) zero_le_one] -- propensity
  change _= _ + (t:ℂ)*(∫ u in (0:ℝ)..1,B u); rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hg u) ((continuous_const.mul hB).intervalIntegrable ..)]
  simp [g]
end YM.MSbar.Pole.Ray
