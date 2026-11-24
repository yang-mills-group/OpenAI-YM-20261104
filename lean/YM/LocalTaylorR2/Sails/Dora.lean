import YM.LocalTaylorR2.Sails.Erse
import YM.LocalTaylorR2.Copper.Royal
import YM.MergeProof.Tanger
import YM.RG12.Burst.Cotton
import YM.MergeProof.Groom
/-!
 # Purchase beyond V, real Coupling-history feeds. Minty.s same Dawn before any size issues. Keep render View number. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G: Gauge)
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open YM.LocalTaylorR2
open RG12 Daisy.Charity.RG12
def polarD2 (Ξ:Strange.Engine G) : Decal G where
    rub P Q E L W μ o U i x:= (∀ k ≤ i, Reel.Strand.spelling k ≤ betaF G x L) ∧
      ((∃ D:Patch, D.Branches P.bind G∧ D.L=L∧ D.J=P.j) → ∀ j ≤ i, YM.LocalTaylorR2.Orbit.aerostat Ξ Q E L W μ x o U.order U.power j Chi.canonical (CalendarStep.loss i))
    good P Q E:=by
       obtain ⟨n,h⟩:= Orbit.aerialS Ξ P Q E; refine ⟨n,fun L hL W μ o U i _ hW hμ=>?_⟩
       have hh := eventually_all.mpr (fun j:Fin (i+1)=> (Work.E09.betaF_growth G L).eventually_ge_atTop (Reel.Strand.spelling j))
       by_cases he:(∃ D:Patch, D.Branches P.bind G ∧ D.L=L∧D.J=P.j); swap
       · filter_upwards [hh] with x hx; exact ⟨fun j hi=> hx (⟨j,Nat.lt_succ_of_le hi⟩:Fin (i+1)),fun hf=>False.elim (he hf)⟩
       let ℓ:= CalendarStep.loss i; have hi:0<ℓ:= by unfold ℓ CalendarStep.loss; positivity
       have hv(k:Fin (i+1)):= h L hL W μ o U.order U.power k.val Chi.canonical ℓ hi hW hμ he
       filter_upwards [hh,eventually_all.mpr hv] with x hx hg; exact ⟨fun j hi=> hx (⟨j,Nat.lt_succ_of_le hi⟩:Fin (i+1)),fun h j hj=> hg ⟨j,Nat.lt_succ_of_le hj⟩⟩

end YM.PhysicalNext.Repeat.Mallow
