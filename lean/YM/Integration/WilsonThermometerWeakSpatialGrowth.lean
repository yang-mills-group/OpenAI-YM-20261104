import YM.Integration.WilsonThermometerWeakSpatialSpare

/-! The nominal finite spatial growth of higher derivatives cancels in
the signed normalization. A single fixed gross power A may be used at each
of the two required derivative orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSpatialGrowth
open Set Filter Function Spec Trace.Pilot OPE OPE.Orbits Climb PhysMS PhysMS.Frame MeasureTheory
open WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff
variable {n:ℕ}
private lemma salary (φ:Test n)(F:Points n→ℂ)(a:ℝ):
    φ.applyTo (a • F)=a • φ.applyTo F:=by
  change (∫x,φ x*(a • F x))=a • ∫x,φ x*F x
  rw [←integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x=>by simp only [Complex.real_smul];ring

private lemma scales (F:Points n→ℂ){x:Points n}(d:ℕ)(smooth:ContDiffAt ℝ ∞ F x)
    {a:ℝ}(ap:0<a):
    ‖iteratedFDeriv ℝ d (a • F) x‖=a*‖iteratedFDeriv ℝ d F x‖:=by
  change ‖iteratedFDeriv ℝ d (fun y=>a • F y) x‖=_
  rw [iteratedFDeriv_const_smul_apply' (a:=a) (smooth.of_le (WithTop.coe_le_coe.mpr le_top)),
      norm_smul,Real.norm_eq_abs,abs_of_pos ap]

theorem original (s A σ:ℝ)(sp:0<s)(An:0≤A)(margin:0<σ)(j:ℕ):
    ∃N:ℕ,j+1<N ∧ ∀(n D:ℕ)(U:Set (Points n)),IsOpen U→U⊆conf n→
    ∀F:ℝ→Points n→ℂ,(∀ᶠr in trail,ContDiffOn ℝ ∞ (F r) U)→
    WilsonThermometerWeakValueRecovery.Signed trail U F (fun r=>r^s) 1 D→
    Price trail U F (fun r=>r^(-A)) 1 ((4*n+D+1)*(N-1)+1)→
    Price trail U F (fun r=>r^(-A)) 1 N→
    ∀{G:Gauge},G.Simple→∀g:ℝ→ℝ,Coupling G g→∀k:ℕ,∀K,IsCompact K→K⊆U→
      ∀ε:ℝ,0<ε→∀ᶠr in trail,∀x∈K,‖iteratedFDeriv ℝ j (F r) x‖≤ε*r^(s-σ)*g r^k:=by
  obtain ⟨N,ot,stage⟩:=WilsonThermometerWeakSpatialSpare.original (s+A) σ (add_pos_of_pos_of_nonneg sp An) margin j
  refine ⟨N,ot,?_⟩
  intro n D U openU clear F smooth issued large curve G simple g running k K compact inside ε ep
  let F' :=fun r:ℝ=>r^A • F r
  have rp:∀ᶠr in trail,(0:ℝ)<r:=self_mem_nhdsWithin
  have grad:∀ᶠr in trail,ContDiffOn ℝ ∞ (F' r) U:=smooth.mono fun r sm=>sm.const_smul (r^A)
  have fresh:WilsonThermometerWeakValueRecovery.Signed trail U F' (fun r=>r^(s+A)) 1 D:=by
    intro L lc li
    obtain ⟨B,Bn,fee⟩:=issued L lc li
    refine ⟨B,Bn,?_⟩
    filter_upwards [fee,rp] with r invoice pos φ whereAt w wp tags
    calc ‖φ.applyTo (F' r)‖=r^A*‖φ.applyTo (F r)‖:=by
            rw [show F' r=r^A • F r from rfl,salary,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos pos _)]
         _≤r^A*(B*(r^s)^1*w):=mul_le_mul_of_nonneg_left (invoice φ whereAt w wp tags) (Real.rpow_nonneg pos.le _)
         _=_:=by rw [pow_one,pow_one,Real.rpow_add pos];ring
  have before (d:ℕ)(pay:Price trail U F (fun r=>r^(-A)) 1 d):
      WilsonThermometerWeakValueRecovery.Bounded trail U F' d:=by
    intro L lc li
    obtain ⟨B,Bn,managed⟩:=pay L lc li
    refine ⟨B,Bn,?_⟩
    filter_upwards [smooth,managed,rp] with r sm funds pos x hx
    rw [show F' r=r^A • F r from rfl,scales (F r) d ((sm x (li hx)).contDiffAt (openU.mem_nhds (li hx))) (Real.rpow_pos_of_pos pos _)]
    calc _≤r^A*(B*(r^(-A))^1):=mul_le_mul_of_nonneg_left (funds x hx) (Real.rpow_nonneg pos.le _)
         _=B:=by rw [pow_one,mul_left_comm (r^A),←Real.rpow_add pos,add_neg_cancel,Real.rpow_zero,mul_one]
  have paid:=stage n D U openU clear F' grad fresh (before _ large) (before _ curve) simple g running k K compact inside ε ep
  filter_upwards [paid,smooth,rp] with r funds sm pos x hx
  apply le_of_mul_le_mul_left (a:=r^A) _ (Real.rpow_pos_of_pos pos A)
  rw [←scales (F r) j ((sm x (inside hx)).contDiffAt (openU.mem_nhds (inside hx))) (Real.rpow_pos_of_pos pos _)]
  calc _≤ε*r^(s+A-σ)*g r^k:=funds x hx
       _=r^A*(ε*r^(s-σ)*g r^k):=by rw [show s+A-σ=(s-σ)+A by ring,Real.rpow_add pos];ring

end YM.Integration.WilsonThermometerWeakSpatialGrowth
end
