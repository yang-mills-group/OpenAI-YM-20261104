import YM.Integration.WilsonMovingForkReporterVanes
import YM.Integration.WilsonThermometerUnitFilingFourWeakWall

/-! Named physical fields on the original tables. Each table uses its own
measured inverse in the input direction and in the reflected invoice. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterPublicNames
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Bel C.book).Hierarchy} {z : Arch C}
  (X : Zoom) (V : ∀ i, Vane C i)

theorem original (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (growth:Tendsto (fun i=>(V i).k) atTop atTop)
    (earned:∀i,(V i).checked f H i) (radius:∀i,(V i).wheel.r=X.r i) :
    ∃ J:Scaling S,J.r=X.r ∧ Scribe f J V z F.sector l F.room.kernel H ∧
      ∀d,∃ B:ℝ,∀ᶠ i in atTop,∀v:S.Field d,∃ y:Arm C S (l:Filter _) d v,
        (∀p,y.source p=heightV V i d p ((J.U i d).symm v)) ∧
        ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt C.S p.1 p.2 (purchaseWidth (V i))
          (C.beta p.1 p.2) (B*‖(J.U i d).symm v‖) (C.O p.1 p.2 (y.source p) 0):=by
  obtain ⟨J,r,book⟩:=WilsonMovingForkReporterVanes.appointed F X V made bliss growth earned radius
  obtain ⟨Y,meter⟩:=book.meters
  refine ⟨J,r,book,fun d=>?_⟩
  obtain ⟨B,bill⟩:=WilsonThermometerUnitFilingFourWeakWall.quote F simple meter d
  refine ⟨B,?_⟩
  filter_upwards [bill,meter.terminal d] with i fee hi v
  obtain ⟨lands,files⟩:=hi
  let a:=(J.U i d).symm v
  have value:(J.U i d) a=v:=(J.U i d).apply_symm_apply _
  have ev:Continuous (fun L:(Bel C.book).Field d →L[ℂ] C.label d=>L a):=
    continuous_id.clm_apply continuous_const
  let y:Arm C S (l:Filter _) d v:=
    ⟨fun p=>heightV V i d p a,Y d i a,ev.continuousAt.tendsto.comp lands,(files a).symm.trans value⟩
  exact ⟨y,fun _=>rfl,fee a⟩

end YM.Integration.WilsonMovingForkReporterPublicNames
end
