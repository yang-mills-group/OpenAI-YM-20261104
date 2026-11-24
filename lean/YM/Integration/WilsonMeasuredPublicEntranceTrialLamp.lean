import YM.Integration.WilsonSeparatedPrefixCanonicalSoft
import YM.Integration.WilsonOriginalOneColorGallery
import YM.Integration.WilsonMeasuredPublicEntranceLampFamily

/-! Each cofactor of the guarded trial is read on its original earned regular
gallery. Its actual masked scalar and every active root can be grouped on
the same numerical chart, with the very same support and signed value. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialLamp
open Function Finset Lattice Wilson RG Ac Marker Push Source Labels
open QuadraticLocal Push.Local Push.AbsoluteSums Extra.Histories MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonOriginalOneColor
open WilsonRetainedMarkedInletRegular
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{p:BudgetPoint}{V I X:Type}[Fintype V][DecidableEq V]{o:V→Site n}{J:Census V}
variable (A:Lamps X I G p o J)(v:V)(x:X)
abbrev leaf := (lamps v A).pullback (fun _:Unit=>x)
local notation "L" => leaf A v x

omit [Fintype V] in
theorem lanes (a:seats v A):(L).mode a=J.fire v:=by
  apply Subtype.ext
  change (A.mode a.val).val={v}
  have live:(A.mode a.val).val.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (fun zero=>A.live a.val (Subtype.ext zero))
  obtain ⟨u,hu⟩:=live
  have small:(A.mode a.val).val⊆{v}:=a.property
  have eu:u=v:=Finset.mem_singleton.mp (small hu)
  exact Finset.Subset.antisymm small (Finset.singleton_subset_iff.mpr (eu ▸ hu))

omit [Fintype V] in
theorem paid {w:V→ℝ}{B:ℕ}{e m:ℝ} (charge:A.Paid w B e m):
    (L).Paid w B e m:=by
  obtain ⟨b,nn,der,spent⟩:=(WilsonOriginalOneColor.regular v A charge).budget
  exact ⟨b,nn,fun i _=>der i x,spent⟩

omit [Fintype V] in
theorem read {w:V→ℝ}{B:ℕ}{e m:ℝ}(wp:∀u,0<w u)(pos:0≤e)(charge:A.Paid w B e m)(U:Config G n):
    (L).log () U=Poly.send (J.fire v) ((A.log x U).part (J.fire v)):=by
  have full:=WilsonOriginalOneColorGallery.log v A x U (charge.sums pos wp x U)
  ext1 s
  by_cases eq:s=J.fire v
  · subst s
    rw [Poly.part_send,if_pos rfl]
    exact (congrArg (fun b:Poly J=>b.part (J.fire v)) full).trans (WilsonOriginalOneColor.own _ _)
  · rw [Poly.part_send,if_neg eq,Lamps.log,Poly.share ((paid A v x charge).sums pos wp () U)]
    simp only [Lamps.frame,Poly.part_send,lanes A v x,if_neg eq,tsum_zero]

theorem grouped [Countable I] (w:V→ℝ)(wp:∀u,0<w u){e m:ℝ}(pos:0≤e)(charge:A.Paid w p.B e m):
    ∃ (c:Poly J) (M:Support n → Config G n → Poly J),
      c.part J.quiet=0 ∧ Poly.price w c≤(Fintype.card V:ℝ)*m ∧
      (∀Z,Burns o Z (M Z) p.threshold) ∧ Towed w id M p.B e m ∧
      ∀U,Poly.send (J.fire v) ((A.log x U).part (J.fire v))=c+∑Z,M Z U:=by
  have pay:=paid A v x charge
  let M:=WilsonPhysicalHistoryGroupedLamps.grouped L {l|¬ (L).clear l} ()
  have total (U) : (∑Z,M Z U)=WilsonPhysicalHistoryGroupedClear.localLog L () U := by
    obtain ⟨_,sum⟩:=(WilsonPhysicalHistoryGroupedLamps.stored L w wp {l|¬ (L).clear l} pos pay ()).repair wp U
    have charged:=(border (L).ground sum).tsum_eq
    rwa [tsum_fintype] at charged
  let C:=WilsonPhysicalHistoryGroupedClear.constant L ()
  have quiet : C.part J.quiet=0 := by
    have ⟨_,summed⟩:=(WilsonPhysicalHistoryGroupedLamps.stored L w wp {l| (L).clear l} pos pay ()).repair wp 1
    change (∑'l,WilsonPhysicalHistoryGroupedLamps.row L {j| (L).clear j} () l 1).part J.quiet=0
    rw [Poly.share summed]
    calc _ = ∑' _l:seats v A,(0:ℂ) := by
           apply tsum_congr
           intro l
           by_cases h:(L).clear l <;> simp [WilsonPhysicalHistoryGroupedLamps.row,h,Lamps.frame,Poly.part_send,Ne.symm ((L).live l)]
         _ = 0 := tsum_zero
  refine ⟨C,M,quiet,WilsonPhysicalHistoryGroupedClear.priced L w wp pos pay (),?_,?_,?_⟩
  · exact WilsonPhysicalHistoryGroupedHealthy.fields L w wp _ pos pay (fun _ h=>h) ()
  · exact WilsonPhysicalHistoryGroupedLamps.original L w wp _ pos pay ()
  · intro U
    rw [total,←WilsonPhysicalHistoryGroupedClear.split L w wp pos pay () U]
    exact (read A v x wp pos charge U).symm

end YM.Integration.WilsonMeasuredPublicEntranceTrialLamp
end
