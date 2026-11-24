import YM.Integration.WilsonMovingForkReporterPublicNames

/-! Named physical fields on the original tables. Each table uses its own
measured inverse in the input direction and in the reflected invoice. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterIntrinsicWage
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Bel C.book).Hierarchy} {z : Arch C}
  (X : Zoom) (V : ∀ i, Vane C i)

theorem original (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (growth:Tendsto (fun i=>(V i).k) atTop atTop)
    (earned:∀i,(V i).checked f H i) (radius:∀i,(V i).wheel.r=X.r i) :
    ∃ J:Scaling S,J.r=X.r ∧ Scribe f J V z F.sector l F.room.kernel H ∧
      ∀d,∃ A B:ℝ,1≤A ∧ 0≤B ∧ ∀ᶠ i in atTop,∀v:S.Field d,
        ‖(J.U i d).symm v‖≤A*cost F d (X.r i) v ∧
        ∃ y:Arm C S (l:Filter _) d v,
          (∀p,y.source p=heightV V i d p ((J.U i d).symm v)) ∧
          ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt C.S p.1 p.2 (purchaseWidth (V i))
            (C.beta p.1 p.2) (B*cost F d (X.r i) v) (C.O p.1 p.2 (y.source p) 0):=by
  obtain ⟨J,r,book,grants⟩:=WilsonMovingForkReporterPublicNames.original
    F X V made simple bliss growth earned radius
  refine ⟨J,r,book,fun d=>?_⟩
  obtain ⟨C,paid⟩:=grants d
  obtain ⟨A,one,wage⟩:=window_prices F simple book.monorail d 1 1 one_pos
  refine ⟨A,max 0 C*A,one,mul_nonneg (le_max_left ..) (zero_le_one.trans one),?_⟩
  filter_upwards [wage,paid] with i axis sold v
  have bound:‖(J.U i d).symm v‖≤A*cost F d (X.r i) v:=by
    simpa only [r,LinearEquiv.apply_symm_apply] using (axis ((J.U i d).symm v)).1
  obtain ⟨y,real,invoice⟩:=sold v
  refine ⟨bound,y,real,?_⟩
  filter_upwards [invoice] with p fee
  refine ⟨fee.live,fee.ticket,fee.mark.trans ?_⟩
  calc C*‖(J.U i d).symm v‖ ≤ max 0 C*‖(J.U i d).symm v‖ :=
         mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)
       _ ≤ max 0 C*(A*cost F d (X.r i) v) := mul_le_mul_of_nonneg_left bound (le_max_left ..)
       _ = _ := (mul_assoc ..).symm

end YM.Integration.WilsonMovingForkReporterIntrinsicWage
end
