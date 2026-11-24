import YM.Integration.WilsonThermometerSolitaryPeers
import YM.Integration.WilsonThermometerSolitaryLampReading

/-! The exchanged seat has no ordinary lamp in its two peers, so its test wage can be changed exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryPeerWage
open Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Extra.Trajectories Next.Rank.Exponential
open WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge} {n:Side} {p:BudgetPoint} {T I I':Type} {o:Fin 3→Site n}

open WilsonThermometerSolitaryPeers

theorem away (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))(v j k:Fin 3)
    (vj:v≠j)(vk:v≠k):∀l,v∉((join a b j k).mode l).val:=by
  intro l
  cases l with
  | inl l => exact fun h=>vj (mem_singleton.mp (l.property h))
  | inr l => exact fun h=>vk (mem_singleton.mp (l.property h))

theorem shifted (E:Lamps T I G p o (J))(v:Fin 3)(w:Fin 3→ℝ)(a:ℝ)(free:∀l,v∉(E.mode l).val)
    {B:ℕ}{α C:ℝ}(paid:E.Paid w B α C):E.Paid (WilsonMeasuredCompanionFace.wage v w a) B α C:=by
  obtain ⟨f,hf,fit,sums⟩:=paid.budget
  refine ⟨f,hf,fit,?_⟩
  change Hit E.ground B (fun l=>Poly.toll (WilsonMeasuredCompanionFace.wage v w a) (E.mode l)*f l) α C
  have scale (l:I):Poly.toll (WilsonMeasuredCompanionFace.wage v w a) (E.mode l)=Poly.toll w (E.mode l):=by
    apply prod_congr rfl
    intro z hz
    have ne:z≠v:=fun e=>free l (e ▸ hz)
    exact if_neg ne
  simpa only [scale] using sums

theorem original [Countable I] [Countable I'] (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))
    (w:Fin 3→ℝ)(hp:∀v,0<w v)(B:ℕ)(α:ℝ)(apos:0≤α)(ea:a.Paid w B α 1)(eb:b.Paid w B α 1)(v:Fin 3):
    ∃ (L:Type) (_:Countable L) (E:Lamps T L G p o (J)),(∀u:ℝ,E.Paid (WilsonMeasuredCompanionFace.wage v (Stoop.radius w 2) u) B α 1) ∧
      (∀l,v∉(E.mode l).val) ∧
      ∀x U, Poly.pass (E.log x U)=peer (fun j=>(a.log x U).part ((J).fire j))
        (fun j=>(b.log x U).part ((J).fire j)) v:=by
  fin_cases v
  · refine ⟨_,inferInstance,join a a 1 2,fun u=>shifted _ _ _ u (away a a 0 1 2 (by decide) (by decide))
        (bought a a 1 2 w hp B α ea ea),away a a 0 1 2 (by decide) (by decide),?_⟩
    exact fun x U=>two a a 1 2 x U (ea.sums apos hp x U) (ea.sums apos hp x U)
  · refine ⟨_,inferInstance,join b a 0 2,fun u=>shifted _ _ _ u (away b a 1 0 2 (by decide) (by decide))
        (bought b a 0 2 w hp B α eb ea),away b a 1 0 2 (by decide) (by decide),?_⟩
    exact fun x U=>two b a 0 2 x U (eb.sums apos hp x U) (ea.sums apos hp x U)
  · refine ⟨_,inferInstance,join b b 0 1,fun u=>shifted _ _ _ u (away b b 2 0 1 (by decide) (by decide))
        (bought b b 0 1 w hp B α eb eb),away b b 2 0 1 (by decide) (by decide),?_⟩
    exact fun x U=>two b b 0 1 x U (eb.sums apos hp x U) (eb.sums apos hp x U)

end YM.Integration.WilsonThermometerSolitaryPeerWage
