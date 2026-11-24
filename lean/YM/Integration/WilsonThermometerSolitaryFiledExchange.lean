import YM.Integration.WilsonThermometerSolitaryPeers
import YM.Integration.WilsonCenteredSingletonMass

/-! Complete held-field exchange on the common physical rep and on each of its seven nonempty faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryFiledExchange
open Function Finset Lattice Wilson RG Ac Labels Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open WilsonThermometerSolitaryExchange WilsonThermometerSolitaryHardPeer
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge} {n:Side} {W:Rep G n} {o:Fin 3→Site n} {T I I':Type}

def value (A:Lamps T I G W.p o (J))(x:T)(U:Config G n)(v:Fin 3):ℂ:=(A.log x U).part ((J).fire v)

/-- The same compensated full source on which all occupied old hard rows are erased. -/
def exit (A:Gallery T I o W (J))(x:T)(U:Config G n)(s:(J).Mode):ℂ:=
  (A.density x U).part s-(W.eval U:ℂ)*(Poly.pass (A.E.log x U)).part s

/-- Retained connected ordinary words with at least two seats, before any assumed first-join estimate. -/
def mixed (A:Gallery T I o W (J))(x:T)(U:Config G n)(s:(J).Mode):ℂ:=
  (W.eval U:ℂ)*((Poly.pass (A.E.log x U)).part s-(word (value A.E x U)).part s)

theorem original [Countable I] [Countable I'] (A:Gallery T I o W (J))(B:Gallery T I' o W (J))
    (w:Fin 3→ℝ)(wp:∀v,0<w v)(κ:ℝ)
    (a:A.E.Paid w W.p.B (W.p.supportExponent+2) 1)(b:B.E.Paid w W.p.B (W.p.supportExponent+2) 1)
    (ka:A.K.Paid w W.p.B W.p.supportExponent κ)(kb:B.K.Paid w W.p.B W.p.supportExponent κ)
    (d:Fin 3→ℕ)(F:∀v,Frame G (d v))(S:∀v,SectionData (F v))(h:∀v,Coefficient (F v) n)
    (test:Fin 3→T→ℂ)(individual:∀v x U,test v x*(h v).density (o v) (S v) W U=
      (A.density x U).part ((J).fire v)-(B.density x U).part ((J).fire v)):
    ∃ (L:Fin 3→Type) (_:∀v,Countable (L v)) (E:∀v,Lamps T (L v) G W.p o (J)),
      (∀v,(E v).Paid (Stoop.radius w 2) W.p.B (W.p.supportExponent+2) 1) ∧
      (∀v x U,Poly.pass ((E v).log x U)=peer (value A.E x U) (value B.E x U) v) ∧
      ∀x U s,(A.density x U).part s-(B.density x U).part s=
        exit A x U s-exit B x U s+(mixed A x U s-mixed B x U s)+
        ∑v,(test v x*(h v).density (o v) (S v) W U*WilsonMeasuredCompanionFace.peers (E v) v s x U+
          (exit (withPeers B v (E v)) x U s-exit (withPeers A v (E v)) x U s)):=by
  have pos:0≤W.p.supportExponent+2:=by linarith only [W.p.exponent_pos]
  choose L count E paid same using WilsonThermometerSolitaryPeers.original A.E B.E w wp W.p.B
    (W.p.supportExponent+2) pos a b
  refine ⟨L,count,E,paid,same,?_⟩
  intro x U s
  let left:=value A.E x U
  let right:=value B.E x U
  let vac:ℂ:=W.eval U
  have sa:=Hard.packet_summing A.K ka W.p.exponent_pos.le wp x U
  have sb:=Hard.packet_summing B.K kb W.p.exponent_pos.le wp x U
  have oneA (v:Fin 3):single vac left (A.density x U) v=
      (Real.exp (W.exponent U):ℂ)*(A.gas x U).part ((J).fire v):=by
    rw [single,WilsonCenteredSingletonMass.ordinary A x U v (a.sums pos wp x U) sa]
    dsimp [left,value,vac]
    ring
  have oneB (v:Fin 3):single vac right (B.density x U) v=
      (Real.exp (W.exponent U):ℂ)*(B.gas x U).part ((J).fire v):=by
    rw [single,WilsonCenteredSingletonMass.ordinary B x U v (b.sums pos wp x U) sb]
    dsimp [right,value,vac]
    ring
  have reads (v:Fin 3):share left right v s=WilsonMeasuredCompanionFace.peers (E v) v s x U:=by
    rw [WilsonMeasuredCompanionFace.peers,same];rfl
  have parts:=WilsonThermometerSolitaryExchange.original vac left right (A.density x U) (B.density x U)
    (fun v=>test v x*(h v).density (o v) (S v) W U) (fun v=>individual v x U) s
  rw [parts]
  have totals:spent vac left (A.density x U) s-spent vac right (B.density x U) s=
      exit A x U s-exit B x U s+(mixed A x U s-mixed B x U s):=by
    dsimp [spent,vac,left,right,exit,mixed];ring
  rw [totals];congr 1
  apply sum_congr rfl
  intro v _
  rw [oneA,oneB,reads,exit,exit,withPeers]
  change _=_+((((withPeers B v (E v)).density x U).part s-vac*(Poly.pass ((E v).log x U)).part s)-
    (((withPeers A v (E v)).density x U).part s-vac*(Poly.pass ((E v).log x U)).part s))
  rw [mode B v (E v) x U s sb,mode A v (E v) x U s sa]
  ring

end YM.Integration.WilsonThermometerSolitaryFiledExchange
