import YM.Integration.WilsonMeasuredSignedActionDirection
import YM.Integration.WilsonOriginalTwoFlatPublicBooks
import YM.TraceExtension.Prom.Zoom.Mast
import YM.TraceExtension.Atlas.Global

/-! The signed trace ray on already issued Wilson reporter tables and their actual
cutoff limits. The sequence of Vanes is an input, including its choice of dates.
The native Ward identity hears the centered image of the six-face action. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOriginalTables
open Function Filter Set Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank Next.UVStress
open WilsonPositionProgramPublicStations WilsonThermometerUnitFilingFourSquare
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {H:(Bel C.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch C}

def Ray (y:S.Field 4):Prop:=∃c:ℝ,0<c ∧ c • centering S 4 y = -lum F

theorem physical (simple:G.Simple)(bliss:Bliss F l Z H)(X:Zoom)(V:∀m:ℕ,Vane C m)
    (checked:∀m,(V m).checked f H m)(radii:∀m,(V m).wheel.r=X.r m)
    (late:Tendsto (fun m=>(V m).k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀ (h : 4 ≤ m), ∃ y : C.label 4,
      Tendsto (fun z:ℕ×ℕ=>(V m).wheel.atCut z (⟨4,Nat.lt_succ_of_le h⟩:Fin (m+1)) (stepField C))
        (l:Filter _) (𝓝 y) ∧ Ray F (S.project 4 y):=by
  obtain ⟨A,eqX,reads,real,issued⟩:=dockedSky F.room.kernel F.room.ordered H F.room.cutoff X V
    checked radii l bliss.lies (cap_given F.room.corrected)
  have mounted:∀m,(V m).wheel.r=A.r m:=fun m=>(radii m).trans (congrFun (congrArg Zoom.r eqX) m).symm
  let pathOfV:StarPath f H A F.room.kernel l:=
    ⟨reads,real,V,late,fun m=>⟨checked m,mounted m⟩,issued⟩
  obtain ⟨W,Y,actual⟩:=gravity F.room.kernel pathOfV
  have signed:=Trace.Pilot.branch_loss F simple (bliss.every A pathOfV W Y actual)
  filter_upwards [issued 4,signed] with m heard sign
  intro hm
  let i:Fin (m+1):=⟨4,Nat.lt_succ_of_le hm⟩
  obtain ⟨B,limits,fields⟩:=heard i rfl
  refine ⟨B i (stepField C),?_,?_⟩
  · exact (continuous_id.clm_apply continuous_const).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mp limits i)
  · rw [←fields (stepField C)]
    exact sign

theorem named (simple:G.Simple)(bliss:Bliss F l Z H)(X:Zoom)(V:∀m:ℕ,Vane C m)
    (checked:∀m,(V m).checked f H m)(radii:∀m,(V m).wheel.r=X.r m)
    (late:Tendsto (fun m=>(V m).k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀ (h : 4 ≤ m) (y : S.Field 4) (arm : Arm C S (l:Filter _) 4 y),
      (∀z,arm.source z=(V m).wheel.atCut z (⟨4,Nat.lt_succ_of_le h⟩:Fin (m+1)) (stepField C)) →
      Ray F y:=by
  filter_upwards [physical F simple bliss X V checked radii late] with m done
  intro hm y arm same
  obtain ⟨v,limits,sign⟩:=done hm
  have agree:arm.label=v:=tendsto_nhds_unique arm.approaches (limits.congr fun z=>(same z).symm)
  rwa [←agree,arm.represents] at sign

end YM.Integration.WilsonMeasuredSignedActionOriginalTables
