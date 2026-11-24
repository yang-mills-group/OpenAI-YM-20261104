import YM.Integration.WilsonPositionProgramSubmittedDates

/-! One cofinal sequence of common finite Wilson position readouts, fixed
independently of the physical upper cutoff, period and fitted fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramReporterBand
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
open private timely from YM.Integration.WilsonPositionProgramSubmittedDates
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "β" => C.family.path.levels.clock.hatBeta

structure Band (stage : ℕ) where
  reporter : ℕ
  lower : ℕ → ℕ
  span : ℕ → ℕ
  upper : ℕ → ℕ
  index : ℕ → ℕ
  powers : ℕ → ℕ → ℕ
  blocks : ∀ t k, (C.family.S.block (lower t+k)).val=D.ratio^(powers t k)
  extent : ∀ t, elapsed (powers t) (span t) = D.reserve*(index t)*(index t)+index t
  ready : ∀ t, stage ≤ lower t
  mature : ∀ t, 1 ≤ β (lower t)
  age : ∀ t, Λ (lower t) ≤ (index t:ℝ)*Real.log D.ratio
  top : ∀ t, lower t+span t=reporter+t+upper t
  higher : ∀ t, 0 < upper t
  spacing : ∀ t, C.family.S.a (reporter+t+upper t)/C.family.S.a (reporter+t)=(D.step (index t)).spacing
  floor : ∀ t, Λ (reporter+t)^((3:ℝ)/2) ≤ (index t:ℝ)*Real.log D.ratio
  ceiling : ∀ t, (index t:ℝ)*Real.log D.ratio ≤ Λ (reporter+t)^((3:ℝ)/2)+2*Λ (reporter+t)
  cofinal : Tendsto index atTop atTop

theorem original (simple : G.Simple) {a : Axis} {ε : ℝ}
    (purchase : WilsonPositionProgramNestedElection.course simple a ε C.kit)
    {d : ℕ} (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) (stage : ℕ) :
    Nonempty (Band C D stage) := by
  obtain ⟨start,w,clock,dates⟩ := WilsonPositionProgramSubmittedDates.original C D simple purchase hd ratio pace
  obtain ⟨n₀,later⟩ := eventually_atTop.mp (dates stage 0)
  let n := fun t : ℕ => n₀+t
  let I := fun t j => elapsed (next w (n t)) j
  have chooseDate (t : ℕ) : ∃ b j, b ≤ n t ∧ 0<j ∧ stage ≤ start+b ∧
      1≤β (start+b) ∧ Λ (start+b)≤(I t j:ℝ)*Real.log D.ratio ∧
      C.family.S.a (start+n t+j)/C.family.S.a (start+n t)=(D.step (I t j)).spacing ∧
      Λ (start+n t)^((3:ℝ)/2) ≤ (I t j:ℝ)*Real.log D.ratio ∧
      (I t j:ℝ)*Real.log D.ratio ≤ Λ (start+n t)^((3:ℝ)/2)+2*Λ (start+n t) ∧
      elapsed w b+D.reserve*(I t j)*(I t j)=elapsed w (n t) ∧
      elapsed (next w b) (n t+j-b)=D.reserve*(I t j)*(I t j)+I t j := by
    obtain ⟨b,hb,j,hj,st,_,β₀,bill,space,lo,hi,before,reached⟩ :=
      later (n t) (Nat.le_add_right n₀ t)
    exact ⟨b,j,hb,hj,st,β₀,bill,space,lo,hi,before,reached⟩
  choose b j data using chooseDate
  refine ⟨⟨start+n₀,(fun t => start+b t),(fun t => n t+j t-b t),j,(fun t => I t (j t)),
    (fun t => next w (b t)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro t k
    simpa only [next,Nat.add_assoc] using clock (b t+k)
  · exact fun t => (data t).2.2.2.2.2.2.2.2.2
  · exact fun t => (data t).2.2.1
  · exact fun t => (data t).2.2.2.1
  · exact fun t => (data t).2.2.2.2.1
  · intro t
    have := (data t).1
    dsimp only [n] at this ⊢
    omega
  · exact fun t => (data t).2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.2.2.1
  · refine tendsto_atTop.2 fun h => ?_
    have grow : Tendsto n atTop atTop := tendsto_atTop_mono (fun t => Nat.le_add_left t n₀) tendsto_id
    filter_upwards [grow.eventually (timely C D simple start w clock 0 h)] with t enough
    obtain ⟨hb,_,_,_,_,_,lo,hi,before,_⟩ := data t
    exact (enough (b t) (I t (j t)) hb lo hi before).2.1
end YM.Integration.WilsonPositionProgramReporterBand
