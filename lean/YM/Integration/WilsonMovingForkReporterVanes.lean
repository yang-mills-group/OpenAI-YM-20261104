import YM.Integration.WilsonPositionProgramPublicStations

/-! Public lifts of a specified sequence of checked original tables. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterVanes
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Bel C.book).Hierarchy} {z : Arch C}
  (X : Zoom) (V : ∀ i, Vane C i)

theorem appointed (made:C.Makes) (bliss:Bliss F l z H)
    (growth:Tendsto (fun i=>(V i).k) atTop atTop)
    (earned:∀i,(V i).checked f H i) (radius:∀i,(V i).wheel.r=X.r i) :
    ∃ J:Scaling S, J.r=X.r ∧ Scribe f J V z F.sector l F.room.kernel H :=by
  obtain ⟨J,path,limit,frame,grant⟩:=dockedSky F.room.kernel F.room.ordered H made
    X V earned radius l bliss.lies (cap_given F.room.corrected)
  have exactRadius:J.r=X.r:=congrArg Zoom.r path
  have season(i): (V i).checked f H i ∧ (V i).wheel.r=J.r i:=
    ⟨earned i,(radius i).trans (congrFun exactRadius i).symm⟩
  have history:StarPath f H J F.room.kernel l:=
    ⟨limit,frame,V,growth,season,grant⟩
  let Reads(d i:ℕ)(Y:(Bel C.book).Field d →L[ℂ] C.label d):Prop:=
    Tendsto (heightV V i d) (l:Filter _) (𝓝 Y) ∧ ∀a,J.U i d a=S.project d (Y a)
  have obtained(d:ℕ):∀ᶠ i in atTop,∃Y,Reads d i Y:=by
    filter_upwards [grant d,eventually_ge_atTop d] with i actual di
    let j:Fin (i+1):=⟨d,Nat.lt_succ_of_le di⟩
    obtain ⟨Z,hZ,points⟩:=actual j rfl
    refine ⟨Z j,?_,points⟩
    exact (tendsto_pi_nhds.mp hZ j).congr (fun w=>by unfold heightV;rw [dif_pos di])
  let Y(d i:ℕ):(Bel C.book).Field d →L[ℂ] C.label d:=
    if h:∃Y,Reads d i Y then h.choose else 0
  have terminal:Gondola f H J l V Y:=by
    refine ⟨growth,season,fun d=>?_⟩
    filter_upwards [obtained d] with i read
    change Reads d i (Y d i)
    simpa only [Y,dif_pos read] using read.choose_spec
  exact ⟨J,exactRadius,bliss.every J history V Y terminal⟩

end YM.Integration.WilsonMovingForkReporterVanes
end
