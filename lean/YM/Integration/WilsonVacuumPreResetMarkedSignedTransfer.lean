import YM.Integration.WilsonVacuumPreResetMarkedNodalCourse

/-! Signed transfer of the entire old quiet and occupied discrepancy
through one original enrolled finite-period coefficient, at all output ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedSignedTransfer
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃M:ℝ,0≤M ∧ ∃d:ℕ,∀Q:Realm G (e+1) Credit.leanC,
    ∀m (hm:Q.anchor ≤ m),v (Q.mint m hm).gear≤Q.cash Credit.leanC m → ∀N (live:m < N) n,
    let p:=cloVent Q m N n hm live 1 zero_lt_one
    let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
    let c:=ratioHigh Q.draws Q.paid N m
    ∀V:PChart G f,(∀j≤e,∀s≤horizon e (r+2*mass k I),∀y,|V j s y|≤1) →
    ∀(K E:family G D)(a:ι→ℝ),(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→∀j≤e,∀s≤horizon e (r+2*mass k I),∀y,
      ‖(K J).1 f j s y‖+‖(E J).1 f j s y‖≤weights a J)→
    ∀t:ℝ,0≤t→t≤1→∀x,
    ‖mist p.wheel p.shadow p.H (p.T p.n) Q.paid (p.W'+t•V) (fun J=>K J+t•E J) c k I i r x-
      mist p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' K c k I i r x‖≤
          M*(gross (Q.y m) f)^d*weights a I*t:=by
  obtain ⟨v,A,Apos,d,price⟩:=WilsonVacuumPreResetMarkedNodalCourse.original G D I k e i r hi
  obtain ⟨B,Bpos,slope⟩:=WilsonVacuumPreResetMarkedTensorSlope.original (D:=D) (G:=G) i I
  refine ⟨v,B*A,mul_nonneg Bpos Apos,d,?_⟩
  intro Q m hm cash N live n p f c V fine K E a hot stock t lo upper x
  let rent:=A*(gross (Q.y m) f)^d*weights a I
  have gp:0≤gross (Q.y m) f:=mul_nonneg (zero_le_one.trans (Q.depth m hm)) (by positivity)
  have rn:0≤rent:=mul_nonneg (mul_nonneg Apos (pow_nonneg gp _)) (positive a (fun j=>(hot j).le) I)
  have nodes(u:ℝ)(unit:|u|≤1):‖mist p.wheel p.shadow p.H (p.T p.n) Q.paid (p.W'+u•V)
      (fun J=>K J+u•E J) c k I i r x‖≤rent:=by
    apply price Q m hm cash N live n V fine u unit (fun J=>K J+u•E J) a hot _ x
    intro J inc alive j hj s hs y
    change ‖(K J).1 f j s y+u•(E J).1 f j s y‖≤_
    apply (norm_add_le ..).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact (add_le_add (le_refl ‖(K J).1 f j s y‖) (mul_le_of_le_one_left (norm_nonneg _) unit)).trans (stock J inc alive j hj s hs y)
  have result:=slope p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' V K E c k r x rent t rn lo upper nodes
  apply result.trans_eq
  dsimp only [rent]
  ring

end YM.Integration.WilsonVacuumPreResetMarkedSignedTransfer
end
