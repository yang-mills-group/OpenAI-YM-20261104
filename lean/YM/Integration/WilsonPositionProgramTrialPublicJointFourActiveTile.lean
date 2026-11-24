import YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveBudget
import YM.Integration.WilsonPositionProgramTrialPublicJointGroundBirth

/-! The genuine incumbent thermal register on the complete active four-field space. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveTile

open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Matrix PowerSeries Finset
open scoped BigOperators Classical
variable {G:Gauge}{F:Frame G 4}

open WilsonPositionProgramTrialFittedLens (matrix)
variable {D k u e:ℕ}{T:SectionData F}{fit:4<D}{H:Hol G}{rails:Rails 4 k u e}
variable {V W Y Z:Credit}

def printed (X:CutsP H T fit rails V W Y Z):Verse F:=
  matrix (Wray X.ax X.tx T fit X.N X.m) (opal F (spools X.ax X.tx X.N k 4 X.m X.i X.pt))

theorem original (H:Hol G)(T:SectionData F)(fit:4<D)(rails:Rails 4 k u e)
    (V W Y Z:Credit)(simple:G.Simple):
    ∃C:Credit,∀X:CutsP H T fit rails V W Y Z,∀q ≤ e,∀i:Alma F,sheet F i ≠ 0 →
      ‖coeff q (printed X i)‖ ≤ C.buy X.Age*X.fuel:=by
  obtain ⟨A,tile⟩:=CutsP.stature H T fit rails V W Y Z
  obtain ⟨B,ink⟩:=WilsonPositionProgramTrialPublicJointFourActiveBudget.currency H T fit e V W Z simple
  refine ⟨B.prodC A,?_⟩
  intro X q depth i live
  let f:ChorusLine H T fit e V W Z:=⟨X.L.L,by rw [←X.he]; exact X.L'.registrar⟩
  let c:CourseS H T fit e V W Z:=⟨f,X.windowC,rfl⟩
  have cap:0 ≤ A.buy X.Age*X.fuel:=
    mul_nonneg (zero_le_one.trans (A.purchase X.windowC.warm)) X.hf
  have ear:=(ink c X.tileP X.tileQ (A.buy X.Age*X.fuel) X.δm cap le_rfl (tile X) q depth i live).main
  have seen:=TallOracle X.L X.ha (X.hc.trans X.hn) X.pt X.sp
  let a:=opal F (spools X.ax X.tx X.N k 4 X.m X.i X.pt)
  have wick (M:Wall F):coeff q (matrix M a i)=(M*ᵥfun j=>coeff q (a j)) i:=by
    simp [matrix,Matrix.mulVec,dotProduct]
  change ‖coeff q (matrix _ a i)‖ ≤ _
  rw [wick,WilsonPhysicalSixWickRows.nonunit X.L.L (by decide) simple (X.hc.trans X.hn |> Nat.le_trans (Nat.le_add_right ..)) X.ha i live]
  change ‖coeff q (opal F (spools _ _ _ _ _ _ _ _) i)‖ ≤ _
  rw [seen,Credit.products,mul_assoc]
  exact ear

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveTile
