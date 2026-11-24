import YM.Integration.WilsonCoherentHeldShelf
import YM.RGComparison.Core16.Spool.Transfer

/-! A uniform finite-period issue. The full normalized complex compact
one-step mark and every analytic ticket use the single presold Wilson shelf. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentFiniteIssue
open Lattice Wilson RG Tree Precision PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router
open RGComparison.Core16 Descent FVA2 FVA2.CityHistory PhysicalNext.Repeat.Legato

variable {G : Gauge} (R : Run G) (i : ℕ)
abbrev stagePatch : Patch := (R.family.path.levels.clock.op i 0).patch
local notation "H₀" => stagePatch R i
local notation "K₀" => R.family.path.levels.clock.kernel

/-- The period and every source placement are chosen after the numerical
admission stage and error constant. Each old mark remains in the common
Haar numerator and shares the original Wilson vacuum denominator. -/
theorem purchased (branches : (H₀).Branches K₀ G) (q : ℝ) (hq : 0<q) :
    ∃ (P : Parcel.Oven H₀) (X : P.Form G), X.Q=q ∧ P.Offers X K₀ ∧
    ∀ {I : Type} [Fintype I] (J : I → Spool.Lamp G) (B : Lumen.Stage) (r : ℕ),
      ∃ (U : Lumen.Stage) (C : ℝ), U.Above B ∧ 0≤C ∧
      ∀ (per : ℕ),
        let S:=R.family.path.levels.clock.op i per
        let D:=Descent.nil (top:=R.family.side (i+1) per)
        ∀ (large : Bid.Larger (G:=G) S) (T : Forest S.ratio) (u : Pins G (R.family.side i per)),
          ‖u‖≤q →
          (∀ o : I → Site (R.family.side (i+1) per),
            Spool.Price U r C (Spool.rank J S T X R.metals.O u o) (Spool.reads J S u o)) ∧
          (Spool.lens (S:=S) u X T).Steady ∧
          ∀ (b : S.Choices) (v : D.Tags) (A : Ticket (Future G S T × Pins G (R.family.side i per))),
            Stack.read u (solenoid S T D v b R.metals.O 1 large (show D.Room G from trivial) A) =
              FVA2.RayScatter.Harvest.page (Spool.lens (S:=S) u X T) R.metals.O u A := by
  obtain ⟨P⟩ := Parcel.Oven.builtafter H₀
  obtain ⟨X,width,paid⟩ := Parcel.Oven.fund (G:=G) (K:=K₀) P branches q hq
  refine ⟨P,X,width,paid,?_⟩
  intro I _ J B r
  obtain ⟨U,C,above,nonneg,all⟩ := Spool.every J paid B r R.alloy.B.ratio
  refine ⟨U,C,above,nonneg,?_⟩
  intro per S D large T u bound
  have inside (e : Edge (Site (R.family.side i per))) : ‖u e‖≤X.Q := by
    rw [width]
    exact (norm_le_pi_norm u e).trans bound
  exact ⟨fun o => all _ _ S.sizes large T u o inside,Spot.runs S T u large P X paid inside,
    fun b v A => Spot.earns_true S T R.metals.O R.alloy.B.ratio b u large v P X paid inside A⟩

end YM.Integration.WilsonCoherentFiniteIssue
end
