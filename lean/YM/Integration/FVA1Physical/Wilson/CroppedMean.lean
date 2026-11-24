import YM.Integration.FVA1Physical.Round2.OrbitWindowReadout

/-! Physical L¹ comparison on the gauge saturation of an open set, with one explicit
exceptional bill and no inverse Haar volume in the error. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set MeasureTheory Lattice RG YM.Wilson
open YM.Integration.FVA1Physical.Round2 YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f:Side}

private theorem window_zero {B:Set (Config G f)} (Q:Config G f → ℝ) (U:Config G f)
    (miss:∀a:Site f→G.El,Lattice.gauge a U∉B) : orbitWindow B Q U = 0 := by
  have num:orbitMean (B.indicator Q) U=0:=by
    unfold orbitMean
    have eq : (fun a:Site f→G.El => B.indicator Q (Lattice.gauge a U)) = 0 := funext fun a=>Set.indicator_of_notMem (miss a) Q
    rw [eq];exact integral_zero ..
  rw [orbitWindow,num,zero_div]

theorem cropped_orbit_mean (μ:Measure (Config G c)) [IsProbabilityMeasure μ]
    (copy:Config G c → Config G f) (cont:Continuous copy) (B:Set (Config G f)) (openB:IsOpen B)
    (P Q:Config G f→ℝ) (pm:Measurable P) (qm:Measurable Q)
    (e K:ℝ) (en:0≤e) (kn:0≤K)
    (price:∀U (a:Site f→G.El),Lattice.gauge a U∈B → |P U-orbitWindow B Q U|≤e) (cap:∀U,|P U|≤K):
    let hot:={u:Config G c | ∃ a:Site f→G.El, Lattice.gauge a (copy u) ∈B}
    (∫ u,|P (copy u)-orbitWindow B Q (copy u)|∂μ) ≤ e+μ.real hotᶜ*K := by
  intro hot
  have owns:IsOpen hot:=by
    have eq:hot=⋃a:Site f→G.El, (fun u=>Lattice.gauge a (copy u)) ⁻¹' B:=by ext; simp [hot]
    rw [eq];apply isOpen_iUnion;intro a;apply openB.preimage
    apply continuous_pi;intro i;unfold Lattice.gauge;fun_prop
  let F:=fun u=>|P (copy u)-orbitWindow B Q (copy u)|
  let fee:=hotᶜ.indicator (fun _=>K)
  have smooth:Measurable F:=((pm.comp cont.measurable).sub
    ((orbitWindow_meas B openB.measurableSet qm).comp cont.measurable)).abs
  have receipt:Integrable fee μ:=(integrable_const K).indicator owns.measurableSet.compl
  have pay (u:Config G c): F u ≤ e+fee u:=by
    by_cases h:u∈hot
    · rw [show fee u=0 from Set.indicator_of_notMem (show u∉hotᶜ from fun ex=>ex h) _]
      rw [add_zero];obtain ⟨a,ha⟩:=h;exact price (copy u) a ha
    · have miss:∀a:Site f→G.El,Lattice.gauge a (copy u)∉B:=fun a hit=>h ⟨a,hit⟩
      rw [show fee u=K from Set.indicator_of_mem h _]
      dsimp only [F];rw [window_zero Q _ miss,sub_zero];linarith only [cap (copy u),en]
  have integr:Integrable F μ:=Integrable.of_bound smooth.aestronglyMeasurable (e+K) (Eventually.of_forall fun u=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (abs_nonneg _)]
    apply (pay u).trans;apply add_le_add le_rfl
    by_cases h:u∈hotᶜ <;> simp [fee,h,kn])
  refine (integral_mono integr ((integrable_const e).add receipt) pay).trans_eq ?_
  change (∫ u,e+fee u ∂μ) = _
  rw [integral_add (integrable_const e) receipt]
  simp [fee,integral_indicator owns.measurableSet.compl,measureReal_def]

end YM.Integration.FVA1Physical.Wilson
