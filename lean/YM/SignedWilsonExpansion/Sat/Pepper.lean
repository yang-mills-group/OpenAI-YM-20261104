import YM.SignedWilsonExpansion.Sat.Pearl
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.SignedWilsonExpansion.Camera
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice Schedules HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Dancer.Shell Dancer.Fort XSpace.Cirrus
open Kane.Tilted Belle Belfry Belfry.ScaleFits StageG
open scoped Topology ContDiff Classical BigOperators
open FVA2.Scale Level Maxwell.Free Future Gauge Dancer.Coats SignedWilsonExpansion.Fire
variable {G:Gauge}{d t n b:ℕ}{ι L J:Type}{ℱ:Filter ι}
open MS MS.Puff MS.High MS.Native MS.Land MS.Fleet MS.Book WilsonCoeffUV.Cosmos.Polestar Precision XSpace.Structure1
variable {c a:Axis}{e u k q h K:ℕ}
open Matrix
namespace Canvass
open Path Wipe
-- fund BOTH placements simultaneously in the same Aperture. Keep all Virtue seats.
open scoped Pointwise
variable (V: Pad (n+1)) (f:Test (n+1)) (b0:Finset Place) (A:Axis)
abbrev sequel (d:ℕ)(c:ℝ)(w:Points d) := c • w
lemma cards (r:ℝ)(h:0<r): ∃ (C:Plans A) (p:C.hired n), V.F⊆interior ( C.Arena n p ).F ∧ MapsTo ( sequel _ r ) V.F ( interior ( C.Arena n p ).F ) ∧ hosts b0 C :=by
    let f:= sequel (n+1) r; let B:= V.F∪ ( f '' V.F ); have v:Path.Roi B:=⟨ V.roi.1.union ( V.roi.1.image ( continuous_const_smul _ ) ), union_subset V.roi.2 (image_subset_iff.mpr (fun x hx=> ?_)) ⟩; case refine_1=> exact Work.A05.smul_conf h ( V.roi.2 hx ) -- possible binder implicit!
    obtain ⟨C,hx⟩:= inhabited ( insert (⟨ n+1,B,v ⟩:Place ) b0 ) A; obtain ⟨p,hP⟩:= hx n B v ( Finset.mem_insert_self .. ); exact ⟨ C,p,( subset_union_left ).trans hP,fun x he=> hP ( Set.mem_union_right _ ( Set.mem_image_of_mem f he ) ),fun n a v he=> hx n a v (Finset.mem_insert_of_mem he) ⟩
lemma diptych (v: Camera.Scale (n+1)) : ∃ (V:Pad (n+1)) (C:Plans A) (p:C.hired n), withinP V v.val ∧ tsupport f ⊆ interior V.F ∧ V.F ⊆ ( C.Arena n p ).F ∧ MapsTo (fun x:Points (n+1)=> (2:ℝ) • x) V.F ( C.Arena n p ).F ∧ hosts b0 C:=by
    obtain ⟨V,hx,ht⟩:= anchor (tsupport f) ⟨ f.hasCompactSupport, f.tsupport_subset ⟩ v.val v.property; obtain ⟨C,p,h,hV,he⟩:= cards V b0 A 2 zero_lt_two; exact ⟨V,C,p, ht,hx,h.trans interior_subset,fun _ h=> interior_subset ( hV h ), he ⟩
end Canvass
end YM.SignedWilsonExpansion.Camera
