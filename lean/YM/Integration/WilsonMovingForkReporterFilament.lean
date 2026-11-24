import YM.Integration.WilsonMovingForkReporterIntrinsicWage
import YM.Integration.WilsonMovingForkReporterRestriction

/-! One physical frame for a growing sequence of already returned cutoff tables. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterFilament
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  {l:Ultrafilter (ℕ×ℕ)} {H:(Bel C.book).Hierarchy} {z:Arch C}
  (F:Final C f S) {D:ℕ→ℕ} (V:∀i,Vane C (D i))

structure Course {D:ℕ→ℕ} (roster:∀i,Vane C (D i)) where
  index : ℕ→ℕ
  cofinal : StrictMono index
  enough (i:ℕ) : i ≤ D (index i)
  zoom : Zoom
  issued (i:ℕ) : zoom.r i = (roster (index i)).wheel.r

def Course.filed {V:∀i,Vane C (D i)} (c:Course V) (i:ℕ) : Vane C i :=
  WilsonMovingForkReporterRestriction.vane (c.enough i) (V (c.index i))

theorem selection (cap:Tendsto D atTop atTop)
    (small:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0)): Nonempty (Course V) := by
  have later (d last:ℕ) : ∃j:ℕ,last<j ∧ d≤D j ∧ (V j).wheel.r < (V last).wheel.r := by
    exact (((eventually_gt_atTop last).and (cap.eventually_ge_atTop d)).and
      (small.eventually (gt_mem_nhds (V last).wheel.rad))).mono
      (fun _ h=>⟨h.1.1,h.1.2,h.2⟩) |>.exists
  choose pick past room below using later
  let q:ℕ→ℕ := Nat.rec (pick 0 0) (fun i prev=>pick (i+1) prev)
  have chain : StrictMono q := strictMono_nat_of_lt_succ (fun i=>past (i+1) (q i))
  have funds (i:ℕ) : i≤D (q i) := by
    cases i with
    | zero => exact room 0 0
    | succ i => exact room (i+1) (q i)
  let X:Zoom := ⟨fun i=>(V (q i)).wheel.r,fun i=>(V (q i)).wheel.rad,
    strictAnti_nat_of_succ_lt (fun i=>below (i+1) (q i)),small.comp chain.tendsto_atTop⟩
  exact ⟨⟨q,chain,funds,X,fun _=>rfl⟩⟩

theorem mounted (c:Course V) (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (late:Tendsto (fun i=>(V i).k) atTop atTop) (honest:∀i,(V i).checked f H (D i)):
    ∃ J:Scaling S,J.r=c.zoom.r ∧ Scribe f J (c.filed) z F.sector l F.room.kernel H ∧
      (∀i (u:Fin (i+1)) (N per:ℕ),(c.filed i).wheel.atCut (N,per) u =
        (V (c.index i)).wheel.atCut (N,per) (WilsonMovingForkReporterRestriction.slot (c.enough i) u)) ∧
      ∀d,∃ A B:ℝ,1≤A ∧ 0≤B ∧ ∀ᶠ i in atTop,∀v:S.Field d,
        ‖(J.U i d).symm v‖≤A*cost F d (c.zoom.r i) v ∧
        ∃ y:Arm C S (l:Filter _) d v,
          (∀p,y.source p=heightV (c.filed) i d p ((J.U i d).symm v)) ∧
          ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt C.S p.1 p.2 (purchaseWidth (c.filed i))
            (C.beta p.1 p.2) (B*cost F d (c.zoom.r i) v) (C.O p.1 p.2 (y.source p) 0) := by
  obtain ⟨J,r,school,issued⟩ := WilsonMovingForkReporterIntrinsicWage.original F c.zoom (c.filed)
    made simple bliss (late.comp c.cofinal.tendsto_atTop)
    (fun i=> WilsonMovingForkReporterRestriction.checked (c.enough i) (V (c.index i)) (honest (c.index i)))
    (fun i=>(c.issued i).symm)
  exact ⟨J,r,school,fun _ _ _ _=>rfl,issued⟩

end YM.Integration.WilsonMovingForkReporterFilament
end
