import YM.Integration.WilsonOriginalFlatOccupiedRate
import YM.Integration.WilsonOriginalOrdinaryFlatHulls
import YM.Integration.WilsonCenteredRegularHit

/-! File the masked-to-uncut discrepancy on the compulsory quiet owners,
then keep the separately paid old regular log in the ordinary face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatFiledMask
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source Labels
open Planned.GuardedAtom Extra.Histories Push Push.AbsoluteSums Pressure ConnectedActivityE6
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner WilsonRootedKioskOccupiedSlip
open WilsonCenteredMixedSetFiling WilsonCenteredCompleteGallery WilsonFullFaceSignedHard
open WilsonCapturedPrimarySoftPartition WilsonFullFaceSignedMasks WilsonOriginalFlatOccupiedRate
open scoped BigOperators Classical
open private YM.Integration.WilsonOriginalFlatOccupiedFace.collect YM.Integration.WilsonOriginalFlatOccupiedFace.subtract
  YM.Integration.WilsonOriginalFlatOccupiedFace.empty from YM.Integration.WilsonOriginalFlatOccupiedFace
open private YM.Integration.WilsonOriginalFlatOccupiedRate.blank from YM.Integration.WilsonOriginalFlatOccupiedRate

variable {n:Side}{G:Gauge}{P:Rep G n}{d:ℕ}{F:Frame G d}{V X ι μ:Type}[DecidableEq V]
    {J:Census V}{o:V→Site n}

def maskBill (p:BudgetPoint)(Z:Support n)(w:V→ℝ)(s:J.Mode)(C D v κ:ℝ):ℝ :=
  ∑q∈shards J s, WilsonFullFaceSignedMasks.charge p Z w C D v κ q

theorem earned (p:BudgetPoint)(Z:Support n)(w:V→ℝ)(hw:∀a,0<w a)(s:J.Mode)
    {C D v κ:ℝ}(cp:0 ≤ C)(dp:0 ≤ D)(hv:0 ≤ v)(div:0<κ)(room:hitWidth p*v ≤ κ)
    {r:ℕ}(load:s.val.card ≤ r):
    Poly.toll w s*maskBill p Z w s C D v κ ≤ roof p Z C r+roof p Z D r:=by
  let h:=hitWidth p*v/κ
  have h0:0 ≤ h:=div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) div.le
  have h1:h ≤ 1:=(div_le_one div).mpr room
  have split:maskBill p Z w s C D v κ=h*(WilsonCapturedPrimarySoftInventory.fare p Z w C s+
      WilsonCapturedPrimarySoftInventory.fare p Z w D s):=by
    unfold maskBill WilsonCapturedPrimarySoftInventory.fare
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun q _=>by unfold WilsonFullFaceSignedMasks.charge h;ring)
  have a:=YM.Integration.WilsonOriginalFlatOccupiedRate.blank p Z w hw s load cp
  have b:=YM.Integration.WilsonOriginalFlatOccupiedRate.blank p Z w hw s load dp
  rw [split,mul_left_comm,mul_add]
  exact (mul_le_of_le_one_left (add_nonneg a.1 b.1) h1).trans (add_le_add a.2 b.2)

variable [Fintype V] [Countable ι]

theorem owned (L:Lamps X ι G P.p o J)(x:X)(s:J.Mode)(Y:Hol G)(Z:Support n)(y:Site n)
    (center:y∈Z)(resident:∀a∈s.val,o a∈Z)(rad:ℕ)(near:∀a∈s.val,separation (o a) y ≤ rad)
    (K:Guard.Keeper P.p P.activities)(w:V→ℝ)(hw:∀a,0<w a){σ C Λ δ v κ E D:ℝ}
    (law:P.Lawful σ C Λ δ v)(hv:0 ≤ v)(room:hitWidth P.p*v ≤ 1)(div:0<κ)
    (paid:L.Paid w P.p.B (P.p.supportExponent+2) E)(gross:Gross L w P.p.B (P.p.supportExponent+2) D):
    Owned (F:=F) P Y y κ (maskBill P.p Z w s E D v κ)
      (fun U=>(P.eval U:ℂ)*((Poly.pass (L.log x U)).part s-(Poly.pass (bare L x U)).part s)):=by
  obtain ⟨q,fit,bill,field⟩:=YM.Integration.WilsonOriginalFlatOccupiedFace.collect (shards J s) law div _ _
    (fun t h=>WilsonReceivedQuietCrownOwner.partition (F:=F) L x s t h y Z center resident rad near
      w hw paid gross K law div hv room Y)
  refine ⟨q,fit,bill,fun U=>?_⟩
  have width:0 ≤ P.p.supportExponent+2:=by linarith only [P.p.exponent_pos]
  rw [field]
  change ∑q∈shards J s,(P.eval U:ℂ)*((∏t∈q.val,(L.log x U).part t.val)-(∏t∈q.val,(bare L x U).part t.val))=_
  change _=(P.eval U:ℂ)*((Poly.pass (L.log x U)).part s-(Poly.pass (bare L x U)).part s)
  rw [YM.RG02.Marks.pass_partition (L.quiet_of_hasSum x U (paid.sums width hw x U)),
    YM.RG02.Marks.pass_partition (WilsonRootedKioskCompleteFiling.quiet L hw width gross x U),
    ←sum_sub_distrib,mul_sum]

def posted (L:Lamps X ι G P.p o J)(Y:Lamps X μ G P.p o J)
    (K:Hard X P.p P.activities.forced P.activities.K o J):Gallery X (ι⊕μ) o P J :=
  ⟨L.join Y,K⟩

/-- The remaining ordinary soft term is a true change of the old log inside
the same partition. Its uniform estimate below charges the original rent. -/
theorem components [Countable μ] (L:Lamps X ι G P.p o J)(Y₀:Lamps X μ G P.p o J)
    (H:Hard X P.p P.activities.forced P.activities.K o J)(x:X)(s:J.Mode)(Y:Hol G)(Z:Support n)(y:Site n)
    (center:y∈Z)(resident:∀a∈s.val,o a∈Z)(rad:ℕ)(near:∀a∈s.val,separation (o a) y ≤ rad)
    (K:Guard.Keeper P.p P.activities)(w:V→ℝ)(hw:∀a,0<w a){σ C Λ δ v κ E D rent:ℝ}
    (law:P.Lawful σ C Λ δ v)(hv:0 ≤ v)(room:hitWidth P.p*v ≤ 1)(div:0<κ)
    (paid:L.Paid w P.p.B (P.p.supportExponent+2) E)(gross:Gross L w P.p.B (P.p.supportExponent+2) D)
    (old:Y₀.Paid w P.p.B (P.p.supportExponent+2) rent)(forced:H.Paid w P.p.B P.p.supportExponent κ)
    {W:ℝ}(source:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹ ≤ W)
    (ep:0 ≤ E)(rp:0 ≤ rent)(wp:0 ≤ W):
    let A:=posted L Y₀ H
    let due:=fee P.p Z w s (E+rent) κ v κ+maskBill P.p Z w s E D v κ
    let rest:=fun U:Config G n=>soft A x s U-(Poly.pass (L.log x U)).part s
    (∀U,‖rest U‖ ≤ WilsonOriginalOrdinaryFlatHulls.change s (W*E) (W*rent)) ∧
    Owned (F:=F) P Y y κ due (fun U=>(A.density x U).part s-
      (P.eval U:ℂ)*((Poly.pass (bare L x U)).part s+rest U)):=by
  intro A due rest
  have width:0 ≤ P.p.supportExponent+2:=by linarith only [P.p.exponent_pos]
  have join (U:Config G n):A.E.log x U=L.log x U+Y₀.log x U:=
    Lamps.joinLog x U (paid.sums width hw x U) (old.sums width hw x U)
  constructor
  · intro U
    apply WilsonOriginalOrdinaryFlatHulls.ordinary s (A.E.log x U) (L.log x U)
      ⟨A.E.quiet_of_hasSum x U ((Lamps.joinPaid paid old).sums width hw x U),
        L.quiet_of_hasSum x U (paid.sums width hw x U)⟩ (mul_nonneg wp ep) (mul_nonneg wp rp)
    intro t ht
    obtain ⟨a,ha⟩:=t.property
    have cash:=WilsonCenteredRegularHit.component L w hw width paid x U t.val a ha
    have debt:=WilsonCenteredRegularHit.component Y₀ w hw width old x U t.val a ha
    have joined:(A.E.log x U).part t.val=(L.log x U).part t.val+(Y₀.log x U).part t.val:=
      congrArg (fun a:Poly J=>a.part t.val) (join U)
    rw [joined,add_sub_cancel_left]
    exact ⟨cash.trans (mul_le_mul_of_nonneg_right (source t ht) ep),
      debt.trans (mul_le_mul_of_nonneg_right (source t ht) rp)⟩
  · have hard:=WilsonOriginalFlatOccupiedFace.owned (F:=F) A x s Y Z y center resident K w hw law hv room div
        (Lamps.joinPaid paid old) forced
    have mask:=owned (F:=F) L x s Y Z y center resident rad near K w hw law hv room div paid gross
    obtain ⟨q,fit,bill,field⟩:=YM.Integration.WilsonOriginalFlatOccupiedFace.subtract law hard
        (YM.Integration.WilsonOriginalFlatOccupiedFace.subtract law
          (YM.Integration.WilsonOriginalFlatOccupiedFace.empty div) mask)
    refine ⟨q,fit,by simpa only [zero_add] using bill,fun U=>?_⟩
    rw [field]
    dsimp only [Pi.sub_apply,Pi.zero_apply,rest]
    ring

end YM.Integration.WilsonOriginalFlatFiledMask
