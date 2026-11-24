import YM.Integration.WilsonMarkedIndependentEnrolledHeatWallet
import YM.Integration.WilsonVacuumPreResetWindingPolynomial
import YM.Integration.WilsonVacuumPreResetWindingTransfer

/-! Simultaneous signed variation of a whole finite marked insertion and
the entire earlier original unmarked action, before its measured reversion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentFiniteSourceSlope
open Function Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatWindow (horizon)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators

private theorem linear {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P T U:PChart G f)(k i r:ℕ)(x):
    reed S F H Q O P k (T-U) i r x=reed S F H Q O P k T i r x-reed S F H Q O P k U i r x:=by
  let W:Pal (ℝ×ℝ) (Woods G f):=fun a l y=>(T a l y,U a l y)
  let first:=LinearMap.fst ℝ ℝ ℝ
  let last:=LinearMap.snd ℝ ℝ ℝ
  have eval (L:ℝ×ℝ→ₗ[ℝ]ℝ):L (reed S F H Q O P k W i r x)=
      reed S F H Q O P k (fun j=>cloaks L (W j)) i r x:=
    congrFun (congrFun (congrFun (reed_maps S F H Q k L) i) r) x
  have p:=eval (first-last)
  have f₁:=eval first
  have f₂:=eval last
  change (reed S F H Q O P k W i r x).1-(reed S F H Q O P k W i r x).2=reed S F H Q O P k (T-U) i r x at p
  change (reed S F H Q O P k W i r x).1=reed S F H Q O P k T i r x at f₁
  change (reed S F H Q O P k W i r x).2=reed S F H Q O P k U i r x at f₂
  rw [f₁,f₂] at p
  exact p.symm

/-- At the receiving side the entire real finite vacuum and every selected
angular/source slot undergo the same affine conditional. A paid finite-vs-folded
quiet error hears the complete original marked cofactor, even in rank zero. -/
theorem original (G:Gauge)(e i l r:ℕ)(hi:i ≤ e):
    ∃(v:Gear G→ℝ)(d:ℕ)(C:ℝ),1 ≤ C ∧ ∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m → ∀N (live:m<N) n,
        let p:=cloVent Q m N n hm live 1 zero_lt_one
        let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
        let previous:=(story Q.draws Q.paid N (m+1)).1 f
        ∀T U:PChart G f,∀η δ A:ℝ,0<η → η ≤ 1 → 0<δ → 0<A →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,|previous j h x-p.W' j h x| ≤ η) →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,|T j h x-U j h x| ≤ δ) →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,|U j h x| ≤ A) →
        ∀x,|reed p.wheel p.shadow p.H (p.T p.n) Q.paid previous l T i r x-
          reed p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' l U i r x| ≤
          C*(gross (Q.y m) f)^d*(δ+A*η):=by
  obtain ⟨v,d,window⟩:=WilsonMarkedIndependentEnrolledHeatWallet.marked G e l r
  obtain ⟨C,nc,lagrange⟩:=WilsonVacuumPreResetWindingTransfer.observed i
  refine ⟨v,d,1+C,by linarith,?_⟩
  intro Q m hm pay N live n p f previous T U η δ A positive small dpos apos prior changed marked x
  let D:PChart G f:=η⁻¹ • (previous-p.W')
  have size:∀j ≤ e,∀h ≤ horizon e (r+2*l),∀y,|D j h y| ≤ 1:=by
    intro j hj h hh y
    change |η⁻¹*(previous j h y-p.W' j h y)| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr positive)]
    exact (mul_le_mul_of_nonneg_left (prior j hj h hh y) (inv_pos.mpr positive).le).trans_eq (inv_mul_cancel₀ positive.ne')
  have start:p.W'+(0:ℝ)•D=p.W':=by simp
  have endpt:p.W'+η•D=previous:=by simp only [D,smul_smul,mul_inv_cancel₀ positive.ne',one_smul];abel
  let Z:=(gross (Q.y m) f)^d
  have coarse_nonneg:0 ≤ Z:=by
    dsimp only [Z,gross]
    exact pow_nonneg (mul_nonneg (zero_le_one.trans (Q.depth m hm)) (by positivity)) _
  obtain ⟨poly,deg,atNode⟩:=WilsonVacuumPreResetWindingPolynomial.occupied p.wheel p.shadow p.H
    (p.T p.n) Q.paid p.W' D U l i r x
  have values(t:ℝ)(ht:|t|≤1):|poly.eval t|≤A*Z:=by
    rw [atNode]
    exact window Q m hm pay N live n D U A apos size marked t ht i hi x
  have debt:=lagrange poly (A*Z) η deg (mul_nonneg apos.le coarse_nonneg) positive.le small values
  simp only [atNode,start,endpt] at debt
  have source:=window Q m hm pay N live n D (T-U) δ dpos size changed η (by simpa [abs_of_pos positive]) i hi x
  rw [endpt,linear] at source
  change |_-_| ≤ δ*Z at source
  have tot:=abs_sub_le (reed p.wheel p.shadow p.H (p.T p.n) Q.paid previous l T i r x)
    (reed p.wheel p.shadow p.H (p.T p.n) Q.paid previous l U i r x)
    (reed p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' l U i r x)
  apply tot.trans
  apply (add_le_add source debt).trans
  change δ*Z+C*(A*Z)*η ≤ (1+C)*Z*(δ+A*η)
  nlinarith [mul_nonneg nc (mul_nonneg dpos.le coarse_nonneg),
    mul_nonneg (mul_nonneg apos.le coarse_nonneg) positive.le]

end YM.Integration.WilsonMarkedIndependentFiniteSourceSlope
end
