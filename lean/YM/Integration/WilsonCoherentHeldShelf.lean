import YM.Integration.WilsonCoherentTraversal

/-! An actual finite Wilson issue for all joint tickets and all held points in
a prespecified ball. The offered shelf is chosen once at that radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentHeldShelf
open Lattice Wilson RG Tree Precision PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router
open RGComparison.Core16 Descent FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato

variable {G : Gauge} (R : Run G) (i per : ℕ)
local notation "S" => R.family.path.levels.clock.op i per
local notation "D" => Descent.nil (top:=R.family.path.levels.S.side (i+1) per)

/-- The offer, including its genuine local norms, is made before every forest,
branch, full signed joint Gaussian ticket, held field and retained grade. -/
theorem purchased (larger : Bid.Larger (G:=G) S) (q : ℝ) (hq : 0 < q) :
    ∃ (P : Parcel.Oven (S).patch) (X : P.Form G),
      X.Q=q ∧ P.Offers X (S).kernel ∧
      ∀ (T : Forest (S).ratio) (b : (S).Choices) (v : (D).Tags)
        (u : Pins G (R.family.path.levels.S.side i per)), ‖u‖ ≤ q →
        (Spool.lens u X T).Steady ∧
        ∀ A : Ticket (Future G S T × Pins G (R.family.path.levels.S.side i per)),
          Stack.read u (solenoid S T D v b R.metals.O 1 larger (show (D).Room G from trivial) A) =
            FVA2.RayScatter.Harvest.page (Spool.lens u X T) R.metals.O u A := by
  obtain ⟨P⟩ := Parcel.Oven.builtafter (S).patch
  obtain ⟨X,width,offer⟩ := Parcel.Oven.fund (G:=G) (K:=(S).kernel) P larger.1 q hq
  refine ⟨P,X,width,offer,?_⟩
  intro T b v u bounded
  have inside (e : Edge (Site (R.family.path.levels.S.side i per))) : ‖u e‖≤X.Q := by
    rw [width]
    exact (norm_le_pi_norm u e).trans bounded
  exact ⟨Spot.runs S T u larger P X offer inside,fun A =>
    Spot.earns_true S T R.metals.O R.alloy.B.ratio b u larger v P X offer inside A⟩

end YM.Integration.WilsonCoherentHeldShelf
end
