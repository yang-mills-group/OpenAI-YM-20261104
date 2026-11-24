import YM.OPE.Compatible.Chain.Vo
/-!
# meter constraints inclusive singular pole other than removed point. Uniform periodic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
def win (p:Site n):ℝ:=‖lit n (lift p)‖
lemma win_p (p:Site n)(h:p≠0):0<win p:= norm_pos_iff.mpr (search.out (searchOn h))
lemma win_gap (p:Site n): leap n * (pdist p:ℝ) ≤ win p:=by
     obtain ⟨i,hi,h⟩:= exists_mem_eq_sup (s:= @univ Axis _) (Finset.univ_nonempty) (f:=fun i=> (lift p i).natAbs); rw [pdist,h]; apply le_trans _ (PiLp.norm_apply_le (lit n (lift p)) i)
     simp [lit,rcast,Real.norm_eq_abs,abs_of_pos (leap_pos n)]
lemma profile (C:KernelChoices)(h:4≤r):∃ B:ℝ,0<B ∧ ∀ v:Train r,∀ n:Side,∀ p:Site n,p≠0→ ∀ x, B*win p^2*sqLength x≤ pairingRe (spline (ShellRow C v) (mon p)) x x :=by
     obtain ⟨a,b,c,ha,hc,H⟩:= Episode.paid C.penalty C.penalty_pos h
     obtain ⟨B,hB,hp⟩:= tank_full ha hc b; refine ⟨B,hB,fun v n p ht x=>?_⟩
     obtain ⟨f,hv⟩:= H v
     have hh:= hp f _ (searchOn ht) x; let I:= lit n (lift p)
     have hZ: tank f I=(↑((win p)^2)⁻¹:ℂ) • spline (ShellRow C v) (mon p) :=by
          unfold tank Further.FreeCovariance.KP.fuel tooth; rw [show mcast I= _ from lit_mon ..,hv,spline_char v h _ (real_frequency p)]; simp [I,spine,win] -- parentheses
     rw [hZ] at hh; rw [show (↑((win p)^2)⁻¹:ℂ)= Complex.ofReal (((win p)^2:ℝ)⁻¹) by norm_cast,pairingRe_scale,inv_mul_eq_div] at hh
     have ht:= (le_div_iff₀ (pow_pos (win_p p ht) 2)).mp hh
     exact (mul_right_comm ..).le.trans ht
lemma entryC {A:Matrix M M ℂ}{d:ℝ}(h:∀ x,d*sqLength x≤ pairingRe A x x)(hv:0<d):∀ i j, ‖A⁻¹ i j‖ ≤ d⁻¹:= by
      intro i j; let t: TypeFace 1→ℂ :=Pi.single j (1:ℂ); let v:=A⁻¹*ᵥ t; have ht : A*ᵥ v=t:=by change A*ᵥ (A⁻¹*ᵥt)=_;rw [mulVec_mulVec,mul_nonsing_inv _ (Value.det_unit hv h),one_mulVec]
      have hk:=h v; unfold pairingRe at hk; rw [ht] at hk; unfold t at hk; simp only [dotProduct_single,mul_one,Pi.star_apply,Complex.star_def, Complex.conj_re] at hk
      have he := hk.trans ((le_abs_self _).trans ((Complex.abs_re_le_norm ..).trans (component_le_length ..))); let s:=Real.sqrt (sqLength v); have hs : s^2=sqLength v:=Real.sq_sqrt (sqLength_nonneg v); have hb:s ≤ d⁻¹:=by
         rw [← one_div, le_div_iff₀ hv]; rw [← hs] at he; by_cases h:s ≤ 0; · exact (mul_nonpos_of_nonpos_of_nonneg h hv.le).trans zero_le_one
         apply (mul_le_mul_iff_left₀ (not_le.mp h)).mp; rw [Real.sqrt_sq (not_le.mp h).le] at he; nlinarith only [he]
      refine le_trans ?_ hb; change _≤ Real.sqrt (sqLength v); rw [show A⁻¹ i j=v i from ?_]; exact component_le_length ..; simp [v,t]
end YM.OPE.Cascade.Terp
