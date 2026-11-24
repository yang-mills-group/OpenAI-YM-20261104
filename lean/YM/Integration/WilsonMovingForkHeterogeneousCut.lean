import YM.Integration.WilsonMovingForkMixedSeed
import YM.Integration.WilsonMovingForkScreenedSites

/-! One physical trial inverse and one deposited compact programme per finite
regulator, selected before a grid node. Every term below is read under the
original normalized Wilson law. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkHeterogeneousCut
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonSeparatedBranchStencil (Trial bill read)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n → ℕ)
local notation "C" => R.family

structure Filed (K:ℕ) where
  station:Fin n → ℕ
  target:ℕ
  before:∀i,station i ≤ K
  A:∀_N _per:ℕ,∀i,(C).label (d i) ≃ₗ[ℂ] (C).label (d i)
  arrived:∀N per,∀live:K < N,∀i e,Arrived R (d i) (station i) K N per target (before i) live.le (1/32) (A N per i) e
  row:∀(_N per:ℕ),((i:Fin n) → (C).label (d i)) → (Fin n → Site ((C).side K per)) →
    ∀i:ℕ,Config G ((C).side i per) → ℂ
  seed:∀N per:ℕ,K < N → ∀w ξ,row N per w ξ K=product R d (N:=N) ξ w

structure Invoice where
  upper:ℝ
  fine:ℕ → ℝ
  across:ℝ
  coarse:ℕ → ℝ
  terminal:ℝ

def Invoice.total (w:Invoice)(v c K:ℕ):ℝ:=
  w.upper+(∑i∈Finset.Ico c K,w.fine i)+w.across+(∑i∈Finset.Ico v c,w.coarse i)+w.terminal

variable {R d}{K:ℕ}(b:Filed R d K){f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{u v c j:ℕ}

def Heard (uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(jK:j ≤ K)
    {x:∀i,S.Field (d i)}(arms:∀i,Arm C S (l:Filter _) (d i) (x i))
    (o:Fin n → Cover)(prediction:Points n → ℂ)(w:Invoice):Prop:=
  ∀ᶠ z:ℕ×ℕ in f.fuse,∀top:K < z.1,
    let a:=fun i=>(arms i).source z
    let q:=doses R d b.station (N:=z.1) (per:=z.2) (b.A z.1 z.2) a
    let ξ:=seats (R:=R) jK z.2 o
    let M:=b.row z.1 z.2 q ξ
    let Y:=word R d j z.1 z.2 (jK.trans top.le) o a
    let raw:=product R d (N:=z.1) ξ q
    let cut:=numerator R z.1 z.2 c (M c)
    let bottom:=numerator R z.1 z.2 v (M v)
    (∀i,v ≤ i → i ≤ K → Integrable (numerator R z.1 z.2 i (M i)) (prior G _)) ∧
    ‖reading R (N:=z.1) (credit C z.1 z.2 0 Y K top.le) u (uv.trans (vc.trans ck))-
      reading R (N:=z.1) (numerator R z.1 z.2 K raw) u (uv.trans (vc.trans ck))‖ ≤ w.upper ∧
    (∀i∈Finset.Ico c K,‖feeAt R z.1 z.2 u M i‖ ≤ w.fine i) ∧
    ‖reading R (N:=z.1) cut u (uv.trans vc)-reading R (N:=z.1) cut v vc‖ ≤ w.across ∧
    (∀i∈Finset.Ico v c,‖feeAt R z.1 z.2 v M i‖ ≤ w.coarse i) ∧
    ‖reading R (N:=z.1) bottom v le_rfl-prediction (tag ((C).S.a j) o)‖ ≤ w.terminal

include F in
theorem site (order:(l:Filter _) ≤ f.fuse)(uj:u ≤ j)(jK:j ≤ K)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)
    {x:∀i,S.Field (d i)}(arms:∀i,Arm C S (l:Filter _) (d i) (x i))
    (o:Fin n → Cover)(gen:tag ((C).S.a j) o∈generic n)(pred:Points n → ℂ)(phase:ℝ)(w:Invoice)
    (stop:∀N per,∀top:j < N,‖gap R N per u (uj.trans top.le)
      (word R d j N per top.le o (fun i=>(arms i).source (N,per)))‖ ≤ phase)
    (wage:Heard (f:=f) b uv vc ck jK arms o pred w):
    ‖S.classMoment S d (tag ((C).S.a j) o) x-pred (tag ((C).S.a j) o)‖ ≤ phase+w.total v c K:=
  WilsonMovingForkMixedSeed.original d F order uj jK uv vc ck x arms b.station o gen (generic_conf n gen)
    b.A b.row b.seed pred phase w.upper w.across w.terminal w.fine w.coarse stop wage

theorem finite (prog:Trial n)(field pred:Points n → ℂ)(ε:ℝ)
    (bounded:∀i:prog.sample,‖field (prog.site i)-pred (prog.site i)‖ ≤ ε):
    ‖read prog field-read prog pred‖ ≤ bill prog*ε:=by
  letI:=prog.count
  unfold WilsonSeparatedBranchStencil.read WilsonSeparatedBranchStencil.bill
  rw [←sum_sub_distrib,sum_mul]
  calc ‖∑i:prog.sample,(prog.weight i • field (prog.site i)-prog.weight i • pred (prog.site i))‖
       ≤ ∑i,‖prog.weight i • field (prog.site i)-prog.weight i • pred (prog.site i)‖:=norm_sum_le .. 
       _ ≤ _:=sum_le_sum fun i _=>by rw [←smul_sub,norm_smul];exact mul_le_mul_of_nonneg_left (bounded i) (norm_nonneg _)

end YM.Integration.WilsonMovingForkHeterogeneousCut
