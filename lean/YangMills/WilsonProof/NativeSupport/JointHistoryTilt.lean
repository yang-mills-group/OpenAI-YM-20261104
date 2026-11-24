import YangMills.WilsonProof.NativeSupport.JointFrozenDirection

/-! Evaluation of the finite marked moment polynomial on the original path.
The temperature displacement is paid by one factor at each actual interior
blocking energy because both temperatures agree at the terminal lag. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset MeasureTheory Lattice RG Wilson Tree RGComparison.Core16 YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators Topology
variable {G : Gauge} {n c : Side}

theorem pathwise_tilt (d:Descent n c) (B Y : ℕ→ℝ) (endValue : Y d.depth=B d.depth)
    (t:d.Tags) (V:Config G c) (x:Descent.Fields G d) (φ:Config G n→ℝ) :
    d.integrand Y t φ V x =
      (∏ q∈interior d,(1+(Real.exp (-(Y (lag d q)-B (lag d q))*cell G d t V x q)-1)))*
        d.integrand B t φ V x := by
  let v (j:ℕ):=Y j-B j
  have line : WilsonUniformUnmarkedInletSignedResponse.line B v 1=Y :=
    funext fun j=>by simp [WilsonUniformUnmarkedInletSignedResponse.line,v]
  have acct : d.account Y t V x=d.account B t V x+d.account v t V x := by
    simpa only [line,one_mul] using WilsonUniformUnmarkedInletSignedResponse.account d B v 1 t V x
  have end0 : v d.depth=0 := sub_eq_zero.mpr endValue
  have factor : (∏ q∈interior d,Real.exp (-(v (lag d q))*cell G d t V x q))=Real.exp (-d.account v t V x) := by
    rw [←Real.exp_sum,middle d v end0]
    simp only [neg_mul,sum_neg_distrib]
  change d.integrand Y t φ V x=(∏ q∈interior d,(1+(Real.exp (-(v (lag d q))*cell G d t V x q)-1)))*d.integrand B t φ V x
  simp_rw [show ∀ z:ℝ,1+(z-1)=z from fun z=>by ring]
  rw [factor]
  simp only [Descent.integrand,acct,neg_add_rev,Real.exp_add]
  ring

private theorem held_env {X : Type*} [MeasurableSpace X] {p:Config G c × X→ℝ}
    (hp:Envelope p) (V:Config G c) : Envelope (fun x=>p (V,x)) := by
  refine ⟨hp.meas.comp (measurable_const.prodMk measurable_id),?_⟩
  obtain ⟨C,bound⟩:=hp.cost
  exact ⟨C,fun x=>bound (V,x)⟩

theorem polynomial_product (d:Descent n c) (ok:d.OK G) (Y:ℕ→ℝ) (V:Config G c)
    (σ:sites n d→ℝ) {φ:Config G n→ℝ} (test:Continuous φ) (I:Finset (sites n d)) (z:ℂ) :
    polynomial I (moment d Y V σ φ) z=∑ t,∫ x,
      (∏ q∈I,(1+z*((σ q*cell G d t V x q:ℝ):ℂ)))*((d.integrand Y t φ V x:ℝ):ℂ) ∂d.measure G := by
  let a (t:d.Tags) (S:Finset (sites n d)) (x:Descent.Fields G d) :=
    (∏ q∈S,σ q * cell G d t V x q)*d.integrand Y t φ V x
  have each (t:d.Tags) (q:sites n d) : Envelope (fun x:Descent.Fields G d=>σ q*cell G d t V x q) :=
    (Envelope.const (σ q)).mul (held_env (cell_envelope d ok t q) V)
  have all (t:d.Tags) (S:Finset (sites n d)) : Envelope (fun x:Descent.Fields G d=>∏ q∈S,σ q*cell G d t V x q) := by
    induction S using Finset.induction_on with
    | empty => simpa using (Envelope.const (1:ℝ) : Envelope (fun _ : Descent.Fields G d=>(1:ℝ)))
    | @insert i S hi ih => simpa only [prod_insert hi] using (each t i).mul ih
  have live (t:d.Tags) (S:Finset (sites n d)) :
      Integrable (fun x=>z^S.card*(a t S x:ℂ)) (d.measure G) :=
    (Complex.ofRealCLM.integrable_comp (((all t S).mul (held_env (d.path_envelope ok Y t φ test) V)).integrable _)).const_mul _
  calc
    _ = ∑ S∈I.powerset,∑ t,∫ x,z^S.card*(a t S x:ℂ) ∂d.measure G := by
      simp only [polynomial,moment,Complex.ofReal_sum,mul_sum,integral_const_mul,integral_complex_ofReal,a]
    _ = ∑ t,∫ x,∑ S∈I.powerset,z^S.card*(a t S x:ℂ) ∂d.measure G := by
      rw [sum_comm]
      exact sum_congr rfl fun t _=>(integral_finsetSum _ fun S _=>live t S).symm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      apply integral_congr_ae
      filter_upwards with x
      rw [prod_one_add,sum_mul]
      apply sum_congr rfl
      intro S _
      simp only [prod_mul_distrib,prod_const,a,Complex.ofReal_mul,Complex.ofReal_prod,mul_assoc]

end YM.Integration.InletSusceptibility.JointMoments
