import YM.Integration.WilsonThermometerWeakJointMoments

/-! Test fees and their signed action for a joint profile centered at a real
configuration. The enlarged support stays inside the separated source collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakProbeTest
open Set Filter Function MeasureTheory Spec Next.UVStress
open scoped Classical BigOperators Topology ContDiff
variable {n:ℕ}

def Charges (f:Test n) (D:ℕ) (w:ℝ):Prop:=
  ∀j, j≤D → ∀x, ‖iteratedFDeriv ℝ j (f : Points n→ℂ) x‖≤w

theorem charge (f:Test n) (D:ℕ):∃w>0,Charges f D w:=by
  have one (j:Fin (D+1)):∃c>0,∀x,‖iteratedFDeriv ℝ j.1 (f:Points n→ℂ) x‖≤c:=by
    obtain ⟨c,hc⟩:=f.hasCompactSupport.exists_bound_of_continuousOn
      (f.contDiff.continuous_iteratedFDeriv (m:=j.1) (WithTop.coe_le_coe.mpr le_top)).continuousOn
    refine ⟨max 1 c,lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun x=>?_⟩
    by_cases hx:x∈tsupport f
    · exact (hc x hx).trans (le_max_right _ _)
    · have zero : iteratedFDeriv ℝ j.1 (f:Points n→ℂ) x=0:=by
        by_contra h; exact hx (support_iteratedFDeriv_subset (𝕜:=ℝ) (f:=(f:Points n→ℂ)) j.1 h)
      rw [zero,norm_zero]; exact zero_le_one.trans (le_max_left _ _)
  choose w pos paid using one
  refine ⟨1+∑ j,w j,add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _=>(pos j).le),fun j hj x=>?_⟩
  let i:Fin (D+1):=⟨j,Nat.lt_succ_of_le hj⟩
  exact (paid i x).trans ((Finset.single_le_sum (fun j _=>(pos j).le) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one))

def probe (f:Test n)(z:Points n){h:ℝ}(pos:0<h)
    (safe:∀x∈tsupport f,z+h • x∈conf n):Test n:=by
  let v:=dilate pos f
  let K:={x:Points n|h⁻¹ • (x-z)∈tsupport f}
  have closed:IsClosed K:=(isClosed_tsupport f).preimage (by fun_prop)
  have hs:tsupport (fun x:Points n=>v (x-z))⊆K:=by
    apply closure_minimal _ closed
    intro x hx; have hv:f (h⁻¹ • (x-z))≠0:=by
      rintro e; exact hx (by change (↑((h^(4*n))⁻¹):ℂ)*f (h⁻¹ • (x-z))=0; rw[e,mul_zero])
    exact subset_tsupport _ hv
  refine ⟨fun x=>v (x-z),v.contDiff.comp (contDiff_id.sub contDiff_const),?_,?_⟩
  · simpa [Function.comp_def,sub_eq_add_neg] using v.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-z))
  · intro x hx
    change x∈conf n
    simpa [smul_inv_smul₀ pos.ne',add_comm z] using safe _ (hs hx)

theorem supported (f:Test n)(z:Points n){h:ℝ}(pos:0<h){K:Set (Points n)}
    (bound:∀x∈tsupport f,z+h • x∈K)(closed:IsClosed K)(clear:K⊆conf n):
    tsupport (probe f z pos (fun x hx=>clear (bound x hx)))⊆K:=by
  apply closure_minimal _ closed
  intro x hx
  have old:f (h⁻¹ • (x-z))≠0:=by
    rintro e; exact hx (by change (↑((h^(4*n))⁻¹):ℂ)*f (h⁻¹ • (x-z))=0; rw[e,mul_zero])
  simpa [smul_inv_smul₀ pos.ne',add_comm z] using bound _ (subset_tsupport _ old)

theorem tested (f:Test n)(z:Points n){h:ℝ}(pos:0<h)(safe)(F:Points n→ℂ):
    (probe f z pos safe).applyTo F=f.applyTo (fun x=>F (z+h • x)):=by
  calc (probe f z pos safe).applyTo F = (dilate pos f).applyTo (fun x=>F (z+x)):=by
         unfold Test.applyTo
         change (∫x:Points n,dilate pos f (x-z)*F x) = _
         rw [←integral_add_right_eq_self (fun x:Points n=>dilate pos f (x-z)*F x) z]
         simp [add_comm z]
       _ = _:=zoom_integral f pos _

theorem priced (f:Test n)(z:Points n){h:ℝ}(pos:0<h)(sm:h≤1)(safe){D:ℕ}{w:ℝ}
    (cash:Charges f D w):Charges (probe f z pos safe) D (h⁻¹^(4*n+D)*w):=by
  intro j hj x
  let g:Points n→ℂ:=fun v=>f (h⁻¹ • v)
  have hf:ContDiff ℝ (j:ℕ) (f:Points n→ℂ):=f.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have sg:ContDiff ℝ (j:ℕ) g:=hf.comp (show ContDiff ℝ (j : ℕ) (fun v : Points n=>h⁻¹ • v) by fun_prop)
  change ‖iteratedFDeriv ℝ j (fun x:Points n=>(↑((h^(4*n))⁻¹):ℂ) • g (x-z)) x‖≤_
  have shifted:ContDiffAt ℝ (j:ℕ) (fun x:Points n=>g (x-z)) x:=(sg.comp (show ContDiff ℝ (j:ℕ) (fun x:Points n=>x-z) by fun_prop)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' (a:=(↑((h^(4*n))⁻¹):ℂ)) shifted,
    norm_smul,iteratedFDeriv_comp_sub]
  have jg:=congrFun (iteratedFDeriv_comp_const_smul (i:=j) h⁻¹ hf) (x-z)
  rw [show iteratedFDeriv ℝ j g (x-z)= _ from jg,norm_smul]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    Real.norm_eq_abs,abs_of_nonneg (by positivity),←mul_assoc,←inv_pow,←pow_add]
  exact mul_le_mul (pow_le_pow_right₀ ((one_le_inv₀ pos).mpr sm) (Nat.add_le_add_left hj _))
    (cash j hj _) (norm_nonneg _) (by positivity)

end YM.Integration.WilsonThermometerWeakProbeTest
end
