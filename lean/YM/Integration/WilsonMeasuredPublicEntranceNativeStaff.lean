import YM.Integration.WilsonMeasuredPublicEntranceNativeProgram
import YM.Integration.WilsonPhysicalWeakWallBounded
import YM.Integration.WilsonPhysicalWeakSundial

/-! The selected original Scribe buys the physically compatible tower and the
finite-degree change of coordinates on its own spatial derivative tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeStaff
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open WilsonPhysicalWeakWallBounded (atBasis slot head cost)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  {Y:Ultrafilter (ℕ×ℕ)}{arch:Trace.Terrace.Arch C}
  (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)

def Receipt (r:ℝ)(U A:tower S)(m:ℕ):Prop:=
  Staff (Y:=Y) h F H r A m ∧ ∀ d ≤ m,∀v:(Bel C.book).Field d,
  ‖(U d).symm (A d v)-v‖ ≤ cost C v * costHint m

theorem along (X:Scaling S){V:∀i,Vane C i}
    (hB:Scribe f X V arch F.sector Y F.room.kernel H):
    ∃ A:ℕ→tower S,∀m:ℕ,∀ᶠ i in atTop,Receipt (Y:=Y) h F H (X.r i) (X.U i) (A i) m:=by
  obtain ⟨A,hA,hT,hα,h₁⟩:=survey h F H X hB
  refine ⟨A,fun m=>?_⟩
  have staffing: ∀ᶠ i in atTop, Staff (Y:=Y) h F H (X.r i) (A i) m:=by
      have he'(n:Fin (m+1))(d:Fin n→Fin (m+1))(w:∀ i,PegC C (d i))(j: Fin (m+1)):= Metric.tendstoUniformlyOn_iff.mp (path_lead F H X hB hA n _ (fun i=> PoleC C (d i) (w i)) j (Scaling.window (sizeHint m) n) (window_closed ..) (fun x hx=>spaced_conf (cost_pos _) hx.1)) _ (cost_pos m)
      filter_upwards [hT,eventually_all.mpr (fun i:Fin (m+1)=>hα i), eventually_all.mpr (fun e:Fin (m+1)=> eventually_all.mpr fun d:Fin (e.val+1)=> h₁ _ _ (Nat.le_of_lt_succ d.isLt)),eventually_all.mpr fun i=> eventually_all.mpr fun d=> eventually_all.mpr fun w=> eventually_all.mpr (he' i d w)] with k hv he h₁ ht
      exact ⟨hv,he,h₁,fun n d v j x hx=> ( (dist_eq_norm ..).symm.trans (dist_comm ..)).trans_le ((ht n d v j x hx).le)⟩
  have basis (b:slot C m):∀ᶠ i in atTop,
      ‖(X.U i b.1).symm (A i b.1 (head C b))-head C b‖≤costHint m:=by
    filter_upwards [Metric.tendsto_nhds.mp (hA b.1 (head C b)) _ (cost_pos m)] with i read
    exact (dist_eq_norm ..).symm.trans_le read.le
  filter_upwards [staffing,eventually_all.mpr basis] with i center reads
  refine ⟨center,fun d hd v=>?_⟩
  exact atBasis (Module.finBasis ℂ ((Bel C.book).Field d)) ((A i d).trans (X.U i d).symm)
    (costHint m) (fun k=>reads ⟨⟨d,Nat.lt_succ_of_le hd⟩,k⟩) v

end YM.Integration.WilsonMeasuredPublicEntranceNativeStaff
end
