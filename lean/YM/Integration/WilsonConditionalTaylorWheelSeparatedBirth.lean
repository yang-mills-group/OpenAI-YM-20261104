import YM.Integration.WilsonConditionalTaylorWheelConnectedRoster
import YM.WilsonCoeffUV.Marked.Bounds.FiniteInterval

/-! Positive-width separated connected bound at a genuine arbitrary birth
b below the cutoff N. The cost of every intervening date is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelSeparatedBirth
open Function Filter Lattice Wilson RG Real
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I]
variable {D k K:I → ℕ} {E:ℕ} {T C:Credit} {Q:Realm G (E+1) T}

def clock (Q:Realm G (E+1) T) (m b:ℕ):ℝ:=Q.y m+snowP Q.draws.S m b+(b-m:ℕ)

def each (D k K:I → ℕ) (E:ℕ) (C T:Credit) (z:ℝ):ℝ:= (tollStep G D k K E C T).buy z

theorem portion {m i b:ℕ} (start:Q.anchor ≤ m) (mi:m ≤ i) (ib:i ≤ b):PadRank Q i b (clock Q m b):=by
  have held:=PadRank.frugal Q start (mi.trans ib)
  exact ⟨fun n p h=>held.year n (mi.trans p) h,
    (Nat.cast_le.mpr (Nat.sub_le_sub_left mi b)).trans held.lengthS⟩

theorem incurred (cl:Cloze D k Q C) (P:Outerm G D) (good:Wellness k P) {m i b N:ℕ}
    (start:Q.anchor ≤ m) (mi:m ≤ i) (ib:i ≤ b) (bN:b ≤ N) (A:ℝ) (A0:0 ≤ A)
    (bought:Uniform Q P b ((start.trans mi).trans ib) A):
    Uniform Q (Gears Q.draws Q.paid K k N b i P) i (start.trans mi)
      (each (G:=G) D k K E C T (clock Q m b)^(b-i)*A):=
  nearFit cl P good (start.trans mi) ib bN bought A0 (portion start mi ib)


theorem field (cl:Cloze D k Q C) (P:Outerm G D) (good:Wellness k P) {m i b N:ℕ}
    (start:Q.anchor ≤ m) (mi:m ≤ i) (ib:i ≤ b) (bN:b ≤ N) (A:ℝ) (A0:0 ≤ A)
    (bought:Uniform Q P b ((start.trans mi).trans ib) A) (p:I → Cover) (J:Finset I)
    (two:1 < J.card) (ρ:ℝ) (apart:cleared Q.draws.S m i ρ p J) (e r:ℕ) (cap:e ≤ E):
    let σ:=(Q.mint i (start.trans mi)).σ
    let Z:=clock Q m b
    let gross:=(each (G:=G) D k K E C T Z^(b-i)*A)^J.card
    Wig Bank.terrain p (σ/2)
      (gross*Real.exp (-(σ/2)*(ρ*Real.exp (snowP Q.draws.S m i)))) J
      ((Gears Q.draws Q.paid K k N b i P p J).2 e r):=by
  intro σ Z gross
  have ticket:Wig Bank.terrain p σ gross J ((Gears Q.draws Q.paid K k N b i P p J).2 e r):=
    incurred (K:=K) cl P good start mi ib bN A A0 bought p J e cap r
  have positive:0 < σ:=(Q.mint i (start.trans mi)).width
  refine ⟨mul_nonneg ticket.1 (Real.exp_pos _).le,fun x=>?_⟩
  have space:=rimD apart mi two x
  have absorbed:=mul_le_mul_of_nonneg_left space (show 0 ≤ σ/2 by positivity)
  calc
    _ ≤ gross*Real.exp (-σ*Syn Bank.terrain p J x):=ticket.2 x
    _ ≤ gross*Real.exp (-(σ/2)*(ρ*Real.exp (snowP Q.draws.S m i)) + -(σ/2)*Syn Bank.terrain p J x):=by
      apply mul_le_mul_of_nonneg_left _ ticket.1
      apply Real.exp_le_exp.mpr
      linarith only [absorbed]
    _=(gross*Real.exp (-(σ/2)*(ρ*Real.exp (snowP Q.draws.S m i))))*Real.exp (-(σ/2)*Syn Bank.terrain p J x):=by
      rw [Real.exp_add,mul_assoc]
end YM.Integration.WilsonConditionalTaylorWheelSeparatedBirth
end
