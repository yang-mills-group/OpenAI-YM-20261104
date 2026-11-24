import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonIndependentMatchedRosterCuts
import YM.Integration.WilsonIndependentMatchedRosterMasks

/-! Common finite headroom for the true Spring and Dormitory on every
signed occurrence pattern of the same moving roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedAdmissions
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos.Polestar
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open scoped BigOperators Classical

theorem length {n:ℕ}(flag:Fin (n+1)→Bool)(h k:ℕ)(hk:h ≤ k):
    ranks flag k h ≤ (n+1)*k ∧ counts flag ≤ n+1:=by
  have ranks' (i:Fin (n+1)):degree (flag i) k h ≤ k:=by
    unfold degree
    split <;> first | exact le_rfl | exact hk
  have marks (i:Fin (n+1)):count (flag i) ≤ 1:=by
    unfold count
    split <;> decide
  constructor
  · calc
      _≤(∑_i:Fin (n+1),k):=sum_le_sum fun i _=>ranks' i
      _=_:=by simp
  · calc
      _≤(∑_i:Fin (n+1),1):=sum_le_sum fun i _=>marks i
      _=_:=by simp

theorem original {G:Gauge}{H:Hol G}{height seats n e u h k out b:ℕ}
    (M:Master H)(R:Realm G (e+1) Credit.leanC)(paid:Elected M R height seats)
    (hk:h ≤ k)(rank:(n+2)*k ≤ out)(depth:out ≤ b)(bond:b ≤ seats)(moment:u ≤ seats)
    (slack:1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-((n+2:ℕ):ℝ)/4):
    SpringD R out u b Credit.leanC ∧
    (∀mask:Bits (n+1),Dormitory R (ranks (choose (n+1) mask) k h) u Credit.leanC) ∧
    (∀mask:Bits (n+1),ranks (choose (n+1) mask) k h ≤ out) ∧
    (∀mask:Bits (n+1),1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-(counts (choose (n+1) mask):ℝ)/4):=by
  have cap (mask:Bits (n+1)):=length (choose (n+1) mask) h k hk
  refine ⟨paid.spring _ _ _ depth bond moment,fun mask=>paid.dorm _ _ ((cap mask).1.trans (rank.trans (depth.trans bond))) moment,
    fun mask=>(cap mask).1.trans rank,?_⟩
  intro mask
  have height':(counts (choose (n+1) mask):ℝ) ≤ ((n+2:ℕ):ℝ):=by exact_mod_cast (cap mask).2
  linarith only [slack,height']

end YM.Integration.WilsonIndependentMovingRosterNormalizedAdmissions

