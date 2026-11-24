import YM.Integration.WilsonOriginalMicroscopicEntranceWholeReading
import YM.Integration.WilsonOriginalMicroscopicEntranceHeadRefund
import YM.Integration.WilsonOriginalMicroscopicEntranceRawTrial

/-! Withdrawal of the two complete ordinary returns on one earlier Wilson field.
The difference still sees the two printed products and the true failed guard at K. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceTwoExits
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address WilsonOriginalNullCorridor Marker
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceGridRow (pin entered old)
open WilsonOriginalMicroscopicEntranceGridStock (old_paid entered_paid)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded gap)
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open OPE.Therm WilsonCoeffUV.Embroider
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}
local notation "J" => Stock.census (Fin 3)
variable (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
    (v:∀a:Fin 3,R.family.label (d a))
local notation "fk" => Nat.le_add_right f n
local notation "topSite" => pin R ((fk).trans live) o
local notation "kSite" => pin R fk o
local notation "atN" => old R d ((fk).trans live) Y o
local notation "atK" => entered R d (N:=N) (n:=n) o v
local notation "guard_" => guarded R d N p (f+n) kSite v

def cutoffFace (s:(J).Mode) : Config G (R.family.side f p)→ℂ :=
  actualTransport R.family (N:=N) (face atN s) ((fk).trans live)

def trialFace (s:(J).Mode) : Config G (R.family.side f p)→ℂ :=
  actualTransport R.family (N:=N) (face atK s) fk

def originalRead (s:(J).Mode){u:ℕ}(uf:u≤f)(W:Config G (R.family.side u p)):ℂ :=
  read R d Y topSite live (uf.trans fk) (raw R d N p (f+n) kSite v) s W

def failedGuard (s:(J).Mode){u:ℕ}(uf:u≤f)(W:Config G (R.family.side u p)):ℂ :=
  units R d (f+n) s * actualTransport R.family (N:=N) (gap R d N p (f+n) kSite v s.val) (uf.trans fk) W

variable {h:Fin 3→ℕ} (s:(J).Mode) (b c:Config G (R.family.side f p)→ℂ) {u:ℕ}(uf:u≤f)(W:Config G (R.family.side u p))

theorem original (κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
    (left:Integrable (fun U=>(R.family.path.rep N p f).eval U • b U) (prior G _))
    (right:Integrable (fun U=>(R.family.path.rep N p f).eval U • c U) (prior G _)):
    originalRead R d live Y o v s uf W -
      (actualTransport R.family (N:=N) b uf W-actualTransport R.family (N:=N) c uf W)=
      actualTransport R.family (N:=N) (cutoffFace R d live Y o s-b) uf W-
      actualTransport R.family (N:=N) (trialFace R d (N:=N) (n:=n) o v s-c) uf W-
      failedGuard R d (N:=N) (n:=n) o v s uf W:=by
  obtain ⟨measN,_,billN⟩:=WilsonOriginalMicroscopicEntranceEarlier.salary atN (old_paid R d live Y o) s
  obtain ⟨measK,_,billK⟩:=WilsonOriginalMicroscopicEntranceEarlier.salary atK (entered_paid R d (N:=N) (n:=n) o v) s
  have a:=actualTransport_weighted_integrable R.family R.makes (le_refl N) measN.aestronglyMeasurable billN ((fk).trans live)
  have b₀:=actualTransport_weighted_integrable R.family R.makes live measK.aestronglyMeasurable billK fk
  have debit₁:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((fk).trans live) a left uf) W
  have debit₂:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((fk).trans live) b₀ right uf) W
  simp only [actualTransport_tower R.family R.makes (le_refl N)] at debit₁
  simp only [actualTransport_tower R.family R.makes live] at debit₂
  have trueMask:=WilsonOriginalMicroscopicEntranceFiling.original R d Y topSite live guard_
    (fun a=>(supplied R d (N:=N) kSite v a).1) (uf.trans fk) s W
  have deposited:(fun U=>units R d (f+n) s*face guard_ s U)=face atK s:=by
    funext U
    simp only [face,units,WilsonOriginalMicroscopicEntranceGridRow.entered,
      WilsonOriginalMicroscopicEntranceGridRow.factor,Finset.prod_mul_distrib]
  rw [deposited] at trueMask
  have crossed:=WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt Y topSite kSite v live (uf.trans fk) s W
  change originalRead R d live Y o v s uf W-read R d Y topSite live (uf.trans fk) guard_ s W= -_ * _ at crossed
  change read R d Y topSite live (uf.trans fk) guard_ s W=actualTransport R.family (N:=N) (face atN s) _ W-_ at trueMask
  unfold cutoffFace trialFace failedGuard
  linear_combination crossed+trueMask-debit₁+debit₂

theorem priced (κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
    (left:Integrable (fun U=>(R.family.path.rep N p f).eval U • b U) (prior G _))
    (right:Integrable (fun U=>(R.family.path.rep N p f).eval U • c U) (prior G _))
    {oldFee trialFee:ℝ}
    (priorBill:‖actualTransport R.family (N:=N) (cutoffFace R d live Y o s-b) uf W‖≤oldFee)
    (trialBill:‖actualTransport R.family (N:=N) (trialFace R d (N:=N) (n:=n) o v s-c) uf W‖≤trialFee):
    ‖originalRead R d live Y o v s uf W -
      (actualTransport R.family (N:=N) b uf W-actualTransport R.family (N:=N) c uf W)‖≤
      oldFee+trialFee+‖failedGuard R d (N:=N) (n:=n) o v s uf W‖:=by
  rw [original R d live Y o v s b c uf W κ pt left right]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add priorBill trialBill)) le_rfl)

end YM.Integration.WilsonOriginalMicroscopicEntranceTwoExits
end
