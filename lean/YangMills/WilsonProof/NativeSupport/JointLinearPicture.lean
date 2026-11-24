import YangMills.WilsonProof.NativeSupport.JointFrozenDirection
import YangMills.WilsonProof.NativeSupport.FrozenWord

/-! Linearity in the actual planted field on the same normalized joint
Wilson law, including its centered mean. This carries all spectator
products and the physical component and test coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset MeasureTheory Lattice RG Wilson RGComparison.Core16 YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedCovariance
open WilsonUniformUnmarkedInletBondCovariances WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators
variable {G:Gauge} {n c:Side} {J:Type}
private theorem held_env {X : Type*} [MeasurableSpace X] {p:Config G c × X→ℝ}
    (hp:Envelope p) (V:Config G c) : Envelope (fun x=>p (V,x)) := by
  refine ⟨hp.meas.comp (measurable_const.prodMk measurable_id),?_⟩
  obtain ⟨C,bound⟩:=hp.cost
  exact ⟨C,fun x=>bound (V,x)⟩

theorem moment_linear (d:Descent n c) (ok:d.OK G) (Y:ℕ→ℝ) (V:Config G c) (σ:sites n d→ℝ)
    (S:Finset (sites n d)) (J₀:Finset J) (a:J→ℝ) (F:J → Config G n→ℝ) (ct:∀ i∈J₀,Continuous (F i)):
    moment d Y V σ (fun X=>∑ i∈J₀,a i*F i X) S=∑ i∈J₀,a i*moment d Y V σ (F i) S := by
  let w (t:d.Tags) (x:Descent.Fields G d):=∏ q∈S,σ q*cell G d t V x q
  have live (t:d.Tags):Envelope (w t):=by
    dsimp only [w]
    induction S using Finset.induction_on with
    | empty=>simpa using (Envelope.const (1:ℝ):Envelope (fun _ : Descent.Fields G d=>(1:ℝ)))
    | @insert i D hi ih=>simp only [prod_insert hi];exact ((Envelope.const (σ i)).mul (held_env (cell_envelope d ok t i) V)).mul ih
  have price (t:d.Tags) (i:J) (hi:i∈J₀):Integrable (fun x:Descent.Fields G d=>w t x*d.integrand Y t (F i) V x) (d.measure G):=
    ((live t).mul (held_env (d.path_envelope ok Y t (F i) (ct i hi)) V)).integrable _
  unfold moment
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl;intro t _
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum]
  · apply integral_congr_ae;filter_upwards with x
    simp only [Descent.integrand,mul_sum]
    apply sum_congr rfl;intro i _;ring
  · intro i hi;exact (price t i hi).const_mul _

theorem moment_picture (d:Descent n c) (ok:d.OK G) (β v:ℕ→ℝ) (V:Config G c) (r:ℝ)
    {F:Config G n→ℝ} (ct:Continuous F) (sym:GaugeInvariant F) (q:sites n d):
    let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
    let z:=mass d Y 1 V
    picture d β v V F r q= -moment d Y V (fun _=>1) F {q}/z+
      (moment d Y V (fun _=>1) F ∅/z)*(moment d Y V (fun _=>1) 1 {q}/z) := by
  intro Y z
  change entry d Y (fun U=>F U-d.conditioned Y F V) V q/z=_
  rw [entry_center d ok Y V ct, fraction d ok Y V ct sym,empty_moment]
  simp only [single_moment,neg_one_mul];dsimp only [z];ring

theorem picture_linear (d:Descent n c) (ok:d.OK G) (β v:ℕ→ℝ) (V:Config G c) (r:ℝ)
    (J₀:Finset J) (a:J→ℝ) (F:J → Config G n→ℝ) (ct:∀ i∈J₀,Continuous (F i)) (sym:∀ i∈J₀,GaugeInvariant (F i)) (q:sites n d):
    picture d β v V (fun X=>∑ i∈J₀,a i*F i X) r q=∑ i∈J₀,a i*picture d β v V (F i) r q := by
  have cs:Continuous (fun X=>∑ i∈J₀,a i*F i X):=continuous_finsetSum _ (fun i hi=>continuous_const.mul (ct i hi))
  have gs:GaugeInvariant (fun X=>∑ i∈J₀,a i*F i X):=fun k X=>sum_congr rfl (fun i hi=>congrArg (a i * ·) (sym i hi k X))
  rw [moment_picture d ok β v V r cs gs,moment_linear d ok _ V _ {q} J₀ a F ct,moment_linear d ok _ V _ ∅ J₀ a F ct]
  simp only [←sum_neg_distrib,sum_div,sum_mul,←sum_add_distrib]
  apply sum_congr rfl;intro i hi
  rw [moment_picture d ok β v V r (ct i hi) (sym i hi)]
  ring

theorem abs_picture_linear (d:Descent n c) (ok:d.OK G) (β v:ℕ→ℝ) (V:Config G c) (r:ℝ)
    (J₀:Finset J) (a:J→ℝ) (F:J → Config G n→ℝ) (ct:∀ i∈J₀,Continuous (F i)) (sym:∀ i∈J₀,GaugeInvariant (F i)) :
    (∑ q∈interior d,|picture d β v V (fun X=>∑ i∈J₀,a i*F i X) r q|) ≤
      ∑ i∈J₀,|a i| *(∑ q∈interior d,|picture d β v V (F i) r q|) := by
  simp_rw [picture_linear d ok β v V r J₀ a F ct sym,mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_le_sum;intro q _
  exact (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun i _=>abs_mul ..)

end YM.Integration.InletSusceptibility.JointMoments
