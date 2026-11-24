import YM.Integration.WilsonMovingForkReporterLeadingFee

/-! Use the same preselected physical leading frame on every issued table and grade. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterCommitted
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  {l:Ultrafilter (ℕ×ℕ)} {H:(Bel C.book).Hierarchy} {z:Arch C}
  (F:Final C f S) {D:ℕ→ℕ} (V:∀i,Vane C (D i))

open WilsonMovingForkReporterFilament

theorem original (J₀:ℝ→tower S) (accepted:Leading F J₀) (c:Course V)
    (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (late:Tendsto (fun i=>(V i).k) atTop atTop) (honest:∀i,(V i).checked f H (D i)):
    ∃ J:Scaling S,J.r=c.zoom.r ∧ Scribe f J c.filed z F.sector l F.room.kernel H ∧
      (∀i (u:Fin (i+1)) (N per:ℕ), (c.filed i).wheel.atCut (N,per) u =
        (V (c.index i)).wheel.atCut (N,per) (WilsonMovingForkReporterRestriction.slot (c.enough i) u)) ∧
      ∀d,∃ A B:ℝ,1≤A ∧ 0≤B ∧ ∀ᶠ i in atTop,∀u:(Bel C.book).Field d,
        let field := J₀ (c.zoom.r i) d u
        ‖(J.U i d).symm field‖ ≤ A*‖u‖ ∧
        ∃ y:Arm C S (l:Filter _) d field,
          (∀p,y.source p=heightV c.filed i d p ((J.U i d).symm field)) ∧
          ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt C.S p.1 p.2 (purchaseWidth (c.filed i))
            (C.beta p.1 p.2) (B*‖u‖) (C.O p.1 p.2 (y.source p) 0) := by
  obtain ⟨J,r,school,rows,incomes⟩ := mounted F V c made simple bliss late honest
  refine ⟨J,r,school,rows,fun d=>?_⟩
  obtain ⟨A,B,one,hB,paid⟩:=incomes d
  obtain ⟨L,large,prices⟩:=WilsonMovingForkReporterLeadingFee.original F J₀ d accepted
  have small:Tendsto c.zoom.r atTop trail:=
    tendsto_nhdsWithin_iff.mpr ⟨c.zoom.limits,Eventually.of_forall c.zoom.positive⟩
  refine ⟨A*L,B*L,one_le_mul_of_one_le_of_one_le one large,mul_nonneg hB (zero_le_one.trans large),?_⟩
  filter_upwards [paid,small.eventually prices] with i grant known u
  have bound:=known u
  obtain ⟨cash,y,named,loans⟩:=grant (J₀ (c.zoom.r i) d u)
  refine ⟨(cash.trans (mul_le_mul_of_nonneg_left bound (zero_le_one.trans one))).trans_eq (mul_assoc ..).symm,
    y,named,?_⟩
  filter_upwards [loans] with p ledger
  exact ⟨ledger.live,ledger.ticket,(ledger.mark.trans (mul_le_mul_of_nonneg_left bound hB)).trans_eq (mul_assoc ..).symm⟩

end YM.Integration.WilsonMovingForkReporterCommitted
end
