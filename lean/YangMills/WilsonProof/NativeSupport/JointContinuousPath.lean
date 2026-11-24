import YangMills.WilsonProof.NativeSupport.JointMarkedPath
import YangMills.WilsonProof.NativeSupport.JointHistoryTilt

/-! The exact original path identity at finite real fugacity. A finite
rescaling used for integration appears on both sides of an equality. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset MeasureTheory Lattice RG Wilson Tree RGComparison.Core16 YM.Pressure Push.BetaTransport
open WilsonUniformUnmarkedInletEnergySites
open scoped Classical BigOperators Topology
variable {G:Gauge} {n c:Side}
theorem marked_scale (d:Descent n c) (β:ℕ → ℝ) (g:Config G n → ℝ) (I:Finset (sites n d))
    (kin:kineticOnly d I) (h:sites n d → ℝ → ℝ) (C:ℝ) (V:Config G c):
    markedOutput d β g I (fun q u=>C*h q u) V=C^I.card*markedOutput d β g I h V := by
  induction d generalizing β with
  | nil=>change I=∅ at kin;rw [kin,card_empty,pow_zero,one_mul];rfl
  | @push m i S T d ih=>
    let D:=Descent.push S T d
    have count:I.card=I.toLeft.card+I.toRight.card:=by
      rw [←card_disjSum,toLeft_disjSum_toRight];rfl
    have rest (U:Config G i):markedOutput d (Descent.upβ β) g I.toRight
        ((fun q u=>C*h q u) ∘ Sum.inr) U=C^I.toRight.card*markedOutput d (Descent.upβ β) g I.toRight (h ∘ Sum.inr) U:=
      ih _ I.toRight kin _ U
    simp only [markedOutput,JointPhysical.push,mul_sum]
    apply sum_congr rfl;intro k _
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with U
    unfold JointPhysical.integrand
    rw [rest]
    have sample:JointPhysical.sample S k I.toLeft ((fun q u=>C*h q u) ∘ Sum.inl) U V=
        C^I.toLeft.card*JointPhysical.sample S k I.toLeft (h ∘ Sum.inl) U V:=by
      simp only [JointPhysical.sample,comp_apply,prod_mul_distrib,prod_const]
    rw [sample,count,pow_add];ring

theorem continuous_path (d:Descent n c) (ok:d.OK G) (β:ℕ → ℝ) {g:Config G n → ℝ} (cg:Continuous g)
    (sym:GaugeInvariant g) (I:Finset (sites n d)) (kin:kineticOnly d I)
    (h:sites n d → ℝ → ℝ) (ct:∀ q,Continuous (h q)) (V:Config G c) :
    markedOutput d β g I h V=d.scalar G β*∑ t,∫ x,payload d I h t V x*d.integrand β t g V x ∂d.measure G := by
  have finite (q:sites n d):∃ c:ℝ,∀ u∈Set.Icc 0 (cap d q),‖h q u‖ ≤ c:=
    isCompact_Icc.exists_bound_of_continuousOn (ct q).continuousOn
  choose c bounded using finite
  let C:=1+∑ q:sites n d,|c q|
  have Cpos:0<C:=by dsimp only [C];positivity
  have all_ (q:sites n d):c q ≤ C:=(le_abs_self _).trans
    ((single_le_sum (fun i _=>abs_nonneg (c i)) (mem_univ q)).trans (le_add_of_nonneg_left zero_le_one))
  let h' (q:sites n d) (u:ℝ):=h q u/C
  have unit (q:sites n d) (u:ℝ) (hu:u∈Set.Icc 0 (cap d q)):‖h' q u‖ ≤ 1:=by
    change ‖h q u/C‖ ≤ 1
    rw [Real.norm_eq_abs,abs_div,abs_of_pos Cpos,div_le_one Cpos]
    exact (bounded q u hu).trans (all_ q)
  have exact_:(fun q u=>C*h' q u)=h:=by funext q u;dsimp [h'];field_simp
  have initial:=marked_scale d β g I kin h' C V
  rw [exact_,marked_path_formula d ok β cg sym I h' (fun q _=>(ct q).measurable.div_const C) (fun q _=>unit q) kin V] at initial
  rw [initial,mul_left_comm,mul_sum]
  congr 1
  apply sum_congr rfl;intro t _
  rw [←integral_const_mul];apply integral_congr_ae
  filter_upwards with x
  rw [←mul_assoc]
  have marked:C^I.card*payload d I h' t V x=payload d I h t V x:=by
    unfold payload
    rw [←prod_const (s:=I) (b:=C),←prod_mul_distrib]
    exact prod_congr rfl fun q _=>congrFun (congrFun exact_ q) _
  rw [marked]

end YM.Integration.InletSusceptibility.JointMoments
