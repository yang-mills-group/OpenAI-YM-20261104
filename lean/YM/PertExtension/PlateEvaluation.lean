import YM.PertExtension.SlotSlope
import YM.PertExtension.TopCalibration

/-! Leading Laurent insertion on an exact Wilson linear fluctuation. Test
before sending the finite volume to infinity. -/
set_option autoImplicit false
set_option maxHeartbeats 1250000
noncomputable section
namespace YM.PertExtension.LatticePT.Slope
open Function Filter Set Wilson Lattice RG Source MeasureTheory Orb GaussianScore Gauge MvPolynomial Heat.Top Drops Bid Labels
open Orb.SlotEvaluation LatticePT.Projection Next.Rank.Spindle
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
local notation "smallG"=> (nhdsWithin (0:ℝ) (Ioi 0))
variable {G:Gauge}{N:Side}(o:Site N)(u:Orb.Dir G N)

theorem isolate {I:ℕ} (P: Pose G I){w:ℕ}(hP:lows P w)(q:ℝ→GaugePanel G I)(W:GaugePanel G I)
    (h:∀ i:Fin I × G.ColorIndex, Tendsto (fun t=>t⁻¹*q t i.1 i.2) smallG (𝓝 ((W i.1) i.2))) :
    Tendsto (fun t:ℝ=> ((t:ℂ)⁻¹)^w * lumin P (q t)) smallG (𝓝 (lumin (cut w P) W)) :=by
    let U (t:ℝ):GaugePanel G I:=t⁻¹ • q t
    let term (m:Fin I×G.ColorIndex→₀ℕ)(t:ℝ)(W:GaugePanel G I):= coeff m P * ((t:ℂ)^(Heat.Top.degree m-w)) * ∏ i∈m.support, ((↑(W i.1 i.2:ℝ):ℂ))^(m i)
    let E(t)(W):=∑ m∈P.support, term m t W
    have hc: Tendsto (fun t:ℝ=> (t:ℂ)) smallG (𝓝 0):=(Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left inf_le_left
    have ht (m)(hm:m∈P.support): Tendsto (fun t=>term m t (U t)) smallG (𝓝 (term m 0 W)) :=by
       simp only [term,Complex.ofReal_zero]
       exact ((hc.pow _).const_mul _).mul <| tendsto_finset_prod _ (fun i hi=>( Complex.continuous_ofReal.continuousAt.tendsto.comp (h i)).pow _)
    have hv : E 0 W=lumin (cut w P) W:=by
       unfold E lumin cut
       simp_rw [MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq, MvPolynomial.support_weightedHomogeneousComponent,Finset.sum_filter,MvPolynomial.coeff_weightedHomogeneousComponent]
       refine Finset.sum_congr rfl fun m hm=>?_
       by_cases hm' : Heat.Top.degree m=w
       · unfold term;rw [hm',Nat.sub_self,pow_zero,mul_one,if_pos hm',if_pos hm'];rfl
       have hz: w<Heat.Top.degree m:=by have h:= hP m hm; rw [degree_eq] at hm' ⊢;omega
       simp only [term,Complex.ofReal_zero,zero_pow (n:=Heat.Top.degree m-w) (by omega),mul_zero,zero_mul,if_neg hm',decide_eq_false hm',ite_false] -- adjust
    rw [←hv]; have hh:= tendsto_finset_sum _ ht
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t h0
    have ht: t≠0 := (show 0<t from h0).ne'
    have Ht : lumin P (q t)=(t:ℂ)^w * E t (U t):=by
       nth_rw 1 [show q t=t • U t by unfold U;rw [smul_smul,mul_inv_cancel₀ ht,one_smul]] -- rewrites U too!
       apply trim_eval P _ hP
    change E _ _ = _; rw [Ht, ← mul_assoc,←mul_pow,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht),one_pow,one_mul]

lemma leg_read {m : ℕ}(P:Pose G m)(W:Fin m → Slot)(ℓ:ℕ): lumin (cut ℓ P) (fun k=>letterPolar (address o (W k)) u) = text (fun p:Atom G=>leg o p u) (rawPart W P ℓ) := by
     unfold leg text rawPart;rw [aeval_rename];simp_rw [Projection.signal_eq,LatticePT.colorBasis,EuclideanSpace.basisFun_inner];rfl
lemma priced_basis {d : ℕ}(F:Labels.Frame G d)(D:Data F)(S:SectionData F)(h:Valid D S)(i:F.Index):
    Tendsto (fun t=>t⁻¹^(F.grades i).2 * fieldAt S i o (representative (t • u))) smallG (𝓝 ((text (fun p:Atom G=>leg o p u) (raw D i)).re)):=by
     let q (t : ℝ):GaugePanel G (D.count i):=fun k=> (D.columns i k).eval (coverAt o (t • u))
     have he : fieldAt S i o ∘ (fun t=>representative (t•u))=(fun t=>(lumin (D.shape i) (q t)).re) := funext fun t=>congr_arg Complex.re (show S.evaluate _ _ = _ from by rw [h i];rfl)
     have hh := isolate (I:=D.count i) (D.shape i) (D.low i) q (fun k=>letterPolar (address o (D.columns i k)) u) (fun k=> ?eq)
     case eq =>
       convert! legible o u (D.columns i k.1,k.2) using 2; apply Eq.symm;exact EuclideanSpace.basisFun_inner G.ColorIndex ℝ (letterPolar (address o (D.columns i k.1)) u) k.2
     have hv := Complex.continuous_re.continuousAt.tendsto.comp hh
     convert! hv using 2; rename_i t; dsimp only [Function.comp_apply]; rw [show fieldAt S i o _=(lumin _ (q t)).re from congr_fun he t,← Complex.ofReal_inv,←Complex.ofReal_pow];simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
     rw [show (raw D i)= rawPart _ _ _ from rfl, leg_read]

end YM.PertExtension.LatticePT.Slope
