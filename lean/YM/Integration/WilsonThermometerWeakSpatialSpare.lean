import YM.Integration.WilsonThermometerWeakSharpPositions
import YM.Integration.WilsonThermometerWeakMeasuredBounds

/-! A signed spatial price r^s with one positive spare σ buys the true
j-th position derivative at r^(s−σ), including every fixed power of the
physical coupling. The finite two higher derivative bills are exposed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSpatialSpare
open Set Filter Function Spec Trace.Pilot OPE OPE.Orbits Climb PhysMS PhysMS.Frame
open WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff
private lemma raised (a:ℝ)(n:ℕ){r:ℝ}(p:0<r):
    (r^a)^n=r^(a*(n:ℝ)):=by rw [←Real.rpow_natCast,←Real.rpow_mul p.le]

theorem original (s σ:ℝ)(sp:0<s)(margin:0<σ)(j:ℕ):
    ∃N:ℕ,j+1<N ∧ ∀(n D:ℕ)(U:Set (Points n)),IsOpen U→U⊆conf n→
    ∀F:ℝ→Points n→ℂ,(∀ᶠr in trail,ContDiffOn ℝ ∞ (F r) U)→
    WilsonThermometerWeakValueRecovery.Signed trail U F (fun r=>r^s) 1 D→
    WilsonThermometerWeakValueRecovery.Bounded trail U F ((4*n+D+1)*(N-1)+1)→
    WilsonThermometerWeakValueRecovery.Bounded trail U F N→
    ∀{G:Gauge},G.Simple→∀g:ℝ→ℝ,Coupling G g→∀k:ℕ,∀K,IsCompact K→K⊆U→
      ∀ε:ℝ,0<ε→∀ᶠr in trail,∀x∈K,‖iteratedFDeriv ℝ j (F r) x‖≤ε*r^(s-σ)*g r^k:=by
  obtain ⟨N,big⟩:=exists_nat_gt (max ((j+1:ℕ):ℝ) (s*(j+1)/σ))
  have fit:j+1<N:=by exact_mod_cast (le_max_left _ _).trans_lt big
  have np:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have slack:s*(j+1)/σ<N:=(le_max_right _ _).trans_lt big
  let a:=s/(N:ℝ)
  have ap:0<a:=div_pos sp np
  have unit:a*(N:ℝ)=s:=by dsimp [a];field_simp [np.ne']
  have small:a*((j+1:ℕ):ℝ)<σ:=by
    have q: s*(j+1)<(N:ℝ)*σ:=(div_lt_iff₀ margin).mp slack
    dsimp [a];push_cast
    field_simp [np.ne'];nlinarith only [q]
  refine ⟨N,fit,?_⟩
  intro n D U openU clear F smooth signed large curve G simple g running k K compact inside ε ep
  let P:=N-(j+1)
  have power:P+j+1=N:=by dsimp [P];omega
  have low:P+j=N-1:=by omega
  let mesh:=fun r:ℝ=>r^a
  have rpos:∀ᶠr in trail,0<r:=self_mem_nhdsWithin
  have mpos:∀ᶠr in trail,0 < mesh r:=rpos.mono fun _ pr=>Real.rpow_pos_of_pos pr a
  have mlim:Tendsto mesh trail (𝓝 0):=by
    have z:Tendsto (fun r:ℝ=>r^a) trail (𝓝 ((0:ℝ)^a)):=
      (Real.continuous_rpow_const ap.le).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [mesh,Real.zero_rpow ap.ne'] using z
  have deployed:WilsonThermometerWeakValueRecovery.Signed trail U F mesh (P+j+1) D:=by
    intro L lc li
    obtain ⟨B,Bn,rent⟩:=signed L lc li
    refine ⟨B,Bn,?_⟩
    filter_upwards [rent,rpos] with r R pos φ sub w wp units
    simpa only [power,mesh,raised a N pos,unit,pow_one] using R φ sub w wp units
  have jet:=WilsonThermometerWeakSharpPositions.original openU clear F mesh P j D mlim mpos
    smooth deployed (by simpa only [low] using large) (by simpa only [power] using curve)
  obtain ⟨B,Bn,earned⟩:=jet K compact inside
  let spare:=a*(P:ℝ)-(s-σ)
  have room:0<spare:=by
    have tot:(P:ℝ)+((j+1:ℕ):ℝ)=N:=by exact_mod_cast (show P+(j+1)=N by omega)
    have both:=congrArg (fun x:ℝ=>a*x) tot
    dsimp [spare];rw [mul_add,unit] at both
    linarith
  have restored:=subpower_payment running simple B spare room ε ep k
  filter_upwards [earned,rpos,restored] with r got pos fee x hx
  have split:mesh r^P=r^spare*r^(s-σ):=by
    change (r^a)^P=_
    rw [raised a P pos,←Real.rpow_add pos];congr 1;dsimp [spare];ring
  calc _≤B*mesh r^P:=got x hx
       _=(B*r^spare)*r^(s-σ):=by rw [split,mul_assoc]
       _≤(ε*g r^k)*r^(s-σ):=mul_le_mul_of_nonneg_right fee (Real.rpow_nonneg pos.le _)
       _=ε*r^(s-σ)*g r^k:=by ring

end YM.Integration.WilsonThermometerWeakSpatialSpare
end
