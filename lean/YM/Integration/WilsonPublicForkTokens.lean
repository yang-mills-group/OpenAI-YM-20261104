import YM.Integration.WilsonPublicForkOrdinary
import YM.Integration.WilsonPublicForkSeats
import YM.Integration.WilsonPublicForkSeats

/-! The nested tree estimate in the original prescription's near/far reading convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkTokens
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open WilsonPublicForkRooms WilsonPublicForkGeometry WilsonPublicForkGeometry.Node
open scoped Topology Classical BigOperators
variable {I:Type} [Fintype I]
local notation "sites" => WilsonPublicForkGeometry.position
local notation "nearSet" => WilsonPublicForkGeometry.near I
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {P:Prescription F.sector.derivatives}
theorem original (bank:LogTrace F P)(p:Node I→C.book.Token)(h:ℕ)(v:Viewers F)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),0<r → r≤t → (∀i,‖x i‖≤M) → ‖z‖≤M → 2*δ≤‖z‖ → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M≤t*δ →
      let X:=sites r t x z
      let A:=spectator F v
      mass p r t*‖observe A (beside (crop X nearSet) (sole (t • z))) (beside (crop p nearSet) (sole (p far)))-
        P.truncated A h (crop X nearSet) (crop p nearSet) 0 (sole (t • z)) (sole (p far))‖ ≤
        b*(badge t*badge r)^K*(t+(r/t)^(h+1)):=by
  obtain ⟨B,K,bp,paid⟩:=WilsonPublicForkOrdinary.original F bank p h v mn dp
  refine ⟨B,K,bp,?_⟩
  filter_upwards [paid] with t cost
  intro r x z rp rt hx hz fz xy room
  let X:=sites r t x z
  have live:=cost r x z rp rt hx hz fz xy room
  obtain ⟨full,inward,outer,outward⟩:=WilsonPublicForkSeats.distinct rp rt dp hx fz xy room
  have table:=(spectate F v).laws.toSymmetric
  have measured:=WilsonPublicForkSeats.full table p X full inward
  have recorded (u:Mode F.sector.derivatives):=WilsonPublicForkSeats.cut P table p X u outer outward
  have merge: (∑u∈bands F.sector.derivatives h,coalesce P nearSet X p child u*
    WilsonPublicForkOrdinary.demand F v X (WilsonPublicForkGeometry.outer I) (update p child (P.letter u)))=
      P.truncated (spectator F v) h (crop X nearSet) (crop p nearSet) 0 (sole (t • z)) (sole (p far)):=by
    apply Finset.sum_congr rfl
    intro u _
    exact congrArg (coalesce P nearSet X p child u * ·) (recorded u)
  change mass p r t*‖WilsonPublicForkOrdinary.demand F v X (frame I).leaves p-_‖≤_ at live
  change mass p r t*‖observe _ _ _-P.truncated _ _ _ _ _ _ _‖≤_
  have eq:=congrArg₂ (fun a b:ℂ=>a-b) measured.symm merge.symm
  exact (congrArg (fun c:ℂ=>mass p r t*‖c‖) eq).trans_le live
end YM.Integration.WilsonPublicForkTokens
end
