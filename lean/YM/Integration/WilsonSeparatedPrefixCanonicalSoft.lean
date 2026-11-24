import YM.Integration.WilsonSeparatedPrefixCanonicalSingleton
import YM.Integration.WilsonOriginalGalleryTwinsField

/-! Single-name expansion on the canonical public calendar. The scalar is
filed separately from the healthy lamps and is kept exactly in every read. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalSoft
open Function Filter Finset MeasureTheory Lattice Wilson RG Ac Marker Push Source Labels
open QuadraticLocal QuadraticLocal.Earn Push.Local Push.AbsoluteSums Extra.Histories MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonOriginalStarPrimaryCatalog
open WilsonRetainedMarkedInletRegular
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V][Fintype V]{J:Census V}{N p k d:ℕ}
local notation "P" => R.family.path.rep N p k
variable (live:k≤N)(ref:R.family.ref d≤k)(o:V → Site (R.family.side k p))(v:V)
  (q:Coefficient (R.family.labels.level d) (R.family.side k p))(fmt:q.Format (o v) R.family.params (R.family.path.rep N p k))
  (w:V → ℝ)(pos:∀i,0<w i){κ B:ℝ}(fee:q.remBound (o v) (R.family.path.rep N p k) κ B)
local notation "L" => WilsonThermometerHostedLamp.enrolled (J:=J) R live ref o v q fmt (fun _:Unit=>(1:ℂ)) (fun _=>True)
local notation "S" => R.family.localSection d

include live ref fmt pos fee in
theorem original (wide:1 ≤ (P).p.supportExponent) :
    let e:=(P).p.supportExponent-1
    let a:=rent R N p k d o v q.x w e+cost (P).p*(w v*B)
    ∃ (c:Poly J) (M:Support (R.family.side k p) → Config G (R.family.side k p) → Poly J),
      c.part J.quiet=0 ∧ Poly.price w c ≤ (Fintype.card V:ℝ)*a ∧
      (∀Z,Burns o Z (M Z) (P).p.threshold) ∧ Towed w id M (P).p.B e a ∧
      ∀U,Poly.send (J.fire v) (q.exponentialEntry (o v) (S) (P) U)=c+∑Z,M Z U := by
  intro e a
  have alpha:0 ≤ e:=sub_nonneg.mpr wide
  have pay:(L).Paid w (P).p.B e a:=WilsonThermometerHostedLamp.complete (J:=J) R live ref o v q fmt (fun _:Unit=>(1:ℂ))
    w pos (by simp) fee
  let M:=WilsonPhysicalHistoryGroupedLamps.grouped L {l|¬ (L).clear l} ()
  have total (U) : (∑Z,M Z U)=WilsonPhysicalHistoryGroupedClear.localLog L () U := by
    obtain ⟨_,sum⟩:=(WilsonPhysicalHistoryGroupedLamps.stored L w pos {l|¬ (L).clear l} alpha pay ()).repair pos U
    have charged:=(border (L).ground sum).tsum_eq
    rwa [tsum_fintype] at charged
  let C:=WilsonPhysicalHistoryGroupedClear.constant L ()
  have quiet : C.part J.quiet=0 := by
    have ⟨_,summed⟩:=(WilsonPhysicalHistoryGroupedLamps.stored L w pos {l| (L).clear l} alpha pay ()).repair pos 1
    change (∑'l,WilsonPhysicalHistoryGroupedLamps.row L {j| (L).clear j} () l 1).part J.quiet=0
    rw [Poly.share summed]
    calc _ = ∑' _l:Bool⊕ℕ,(0:ℂ) := by
           apply tsum_congr
           intro l
           by_cases h:(L).clear l <;> simp [WilsonPhysicalHistoryGroupedLamps.row,h,Lamps.frame,Poly.part_send,Ne.symm ((L).live l)]
         _ = 0 := tsum_zero
  refine ⟨C,M,quiet,WilsonPhysicalHistoryGroupedClear.priced L w pos alpha pay (),?_,?_,?_⟩
  · exact WilsonPhysicalHistoryGroupedHealthy.fields L w pos _ alpha pay (fun _ h=>h) ()
  · exact WilsonPhysicalHistoryGroupedLamps.original L w pos _ alpha pay ()
  · intro U
    rw [total,←WilsonPhysicalHistoryGroupedClear.split L w pos alpha pay () U]
    have one:=WilsonThermometerHostedLamp.full (J:=J) R live ref o v q fmt (fun _:Unit=>(1:ℂ)) w pos
      (by simp) fee wide () U
    simp only [one_mul] at one
    ext m
    by_cases hit:m=J.fire v
    · subst m
      rw [Poly.part_send,if_pos rfl,one]
    · rw [Poly.part_send,if_neg hit,Lamps.log,Poly.share (pay.sums alpha pos () U)]
      simp only [Lamps.frame,Poly.part_send,WilsonThermometerHostedLamp.modes,if_neg hit,tsum_zero]

end YM.Integration.WilsonSeparatedPrefixCanonicalSoft
end
