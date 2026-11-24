import YM.Integration.WilsonThermometerWeakPairDistinct
import YM.Integration.WilsonThermometerWeakPairSeats

/-! The nested tree estimate in the original prescription's near/far reading convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairTokens
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open WilsonThermometerWeakPairRooms WilsonThermometerWeakPairFork
open scoped Topology Classical BigOperators
local notation "sites" => WilsonThermometerWeakPairFork.position
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {P:Prescription F.sector.derivatives}
theorem original (bank:LogTrace F P)(p:Fin 5→C.book.Token)(h:ℕ)(v:Viewers F)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x y z:E4),0<r → r≤t → ‖x‖≤M →
      ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ → r*M≤t*δ →
      let X:=sites r t x y z
      let A:=spectator F v
      mass p r t*‖observe A (beside (crop X near) (sole (t • z))) (beside (crop p near) (sole (p 4)))-
        P.truncated A h (crop X near) (crop p near) 0 (sole (t • z)) (sole (p 4))‖ ≤
        b*(badge t*badge r)^K*(t+(r/t)^(h+1)):=by
  obtain ⟨B,K,bp,paid⟩:=WilsonThermometerWeakPairOrdinary.original F bank p h v mn dp
  refine ⟨B,K,bp,?_⟩
  filter_upwards [paid] with t cost
  intro r x y z rp rt hx hy hz fz xy room
  let X:=sites r t x y z
  have live:=cost r x y z rp rt hx hy hz fz xy room
  obtain ⟨full,inward,outer,outward⟩:=WilsonThermometerWeakPairDistinct.actual rp rt dp hx hy fz xy room
  have table:=(spectate F v).laws.toSymmetric
  have measured:=WilsonThermometerWeakPairSeats.full table p X full inward
  have recorded (u:Mode F.sector.derivatives):=WilsonThermometerWeakPairSeats.cut P table p X u outer outward
  have merge: (∑u∈bands F.sector.derivatives h,coalesce P near X p 1 u*
    WilsonThermometerWeakPairOrdinary.demand F v X WilsonThermometerWeakPairRooms.outside (update p 1 (P.letter u)))=
      P.truncated (spectator F v) h (crop X near) (crop p near) 0 (sole (t • z)) (sole (p 4)):=by
    apply Finset.sum_congr rfl
    intro u _
    exact congrArg (coalesce P near X p 1 u * ·) (recorded u)
  change mass p r t*‖WilsonThermometerWeakPairOrdinary.demand F v X frame.leaves p-_‖≤_ at live
  change mass p r t*‖observe _ _ _-P.truncated _ _ _ _ _ _ _‖≤_
  have eq:=congrArg₂ (fun a b:ℂ=>a-b) measured.symm merge.symm
  exact (congrArg (fun c:ℂ=>mass p r t*‖c‖) eq).trans_le live
end YM.Integration.WilsonThermometerWeakPairTokens
end
