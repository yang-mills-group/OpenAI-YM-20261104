import YM.Integration.WilsonIndependentCollarEventQuote

/-! A finite staged pupil menu for the original post-length gear. Every
retained subset and component can be chosen independently before the run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarEventMenu
open Finset WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos Wilson RG
open scoped BigOperators Classical
variable {G:Gauge}

structure Request (G:Gauge) where
  names : ℕ
  D : Fin names → ℕ
  k : Fin names → ℕ
  order : ℕ
  q : ℕ
  r : ℕ
  grade : q ≤ order
  subset : Finset (Fin names)
  front : Fin names
  present : front ∈ subset
  inlet : Gear G → ℝ
  positive : ∀I,0 < inlet I

def Request.price (P:Request G)(I:Gear G):ℝ:=
  WilsonIndependentCollarEventQuote.localPrice (D:=P.D) (k:=P.k) P.order P.q P.r P.grade
    P.subset P.front P.present P.inlet P.positive I

def price {α:Type*} (live:ℕ→Finset α)(request:ℕ→α→Request G)(stage:ℕ)(I:Gear G):ℝ:=
  ∑ k∈live stage,max 0 ((request stage k).price I)

theorem charged {α:Type*}(live:ℕ→Finset α)(request:ℕ→α→Request G)
    {stage:ℕ}{I:Gear G}{j:α}{z:ℝ}(hj:j∈live stage)
    (enrolled:price live request stage I≤z) : (request stage j).price I≤z :=
  ((le_max_right ..).trans (single_le_sum (f:=fun a=>max 0 ((request stage a).price I))
    (fun _ _=>le_max_left ..) hj)).trans enrolled

end YM.Integration.WilsonIndependentCollarEventMenu
