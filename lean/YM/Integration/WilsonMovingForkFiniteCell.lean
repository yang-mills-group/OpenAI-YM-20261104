import YM.Integration.WilsonMovingForkShiftedSite

/-! The genuine fitted columns and the entire independent prediction may
depend on the original cutoff and period. Retain that dependence through
the centered finite scalar before taking the physical limits. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.WilsonMovingForkFiniteCell
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonMovingForkHeterogeneousCut (Invoice Filed Heard)
open WilsonMovingForkMixedSeed (doses product)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonPublicForkTrialHearing
open WilsonMovingForkShiftedSite (Reached)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  {l:Ultrafilter (ℕ×ℕ)}{j n u v c K:ℕ}{d:Fin n→ℕ}{x:∀i,S.Field (d i)}
  (file:Filed R d K)(arms:∀i,Arm R.family S (l:Filter _) (d i) (x i))
  (jK:j≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)
local notation "C" => R.family

/-- The upper fee uses the attained physical optical matrix at this very
cutoff and the fully restored simultaneous K input. -/
def Upper (s:Fin n → Cover)(z:ℕ×ℕ)(top:K<z.1)(B:ℝ):Prop:=
  let a:=fun i=>(arms i).source z
  let q:=doses R d file.station (N:=z.1) (per:=z.2) (file.A z.1 z.2) a
  let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jK z.2 s
  let Y:=word R d j z.1 z.2 (jK.trans top.le) s a
  let raw:=product R d (N:=z.1) ξ q
  ‖reading R (N:=z.1) (credit (C) z.1 z.2 0 Y K top.le) u (uv.trans (vc.trans ck))-
    reading R (N:=z.1) (numerator R z.1 z.2 K raw) u (uv.trans (vc.trans ck))‖≤B

/-- Every genuine later charge is separate from the original upper
replacement and is heard on its named normalized Wilson receiver. -/
def Later (s:Fin n → Cover)(z:ℕ×ℕ)(I:ℂ)(w:Invoice):Prop:=
  let a:=fun i=>(arms i).source z
  let q:=doses R d file.station (N:=z.1) (per:=z.2) (file.A z.1 z.2) a
  let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jK z.2 s
  let M:=file.row z.1 z.2 q ξ
  let cut:=numerator R z.1 z.2 c (M c)
  let floor:=numerator R z.1 z.2 v (M v)
  (∀i, v ≤ i → i ≤ K → Integrable (numerator R z.1 z.2 i (M i)) (prior G _)) ∧
  (∀i∈Finset.Ico c K,‖feeAt R z.1 z.2 u M i‖≤w.fine i) ∧
  ‖reading R (N:=z.1) cut u (uv.trans vc)-reading R (N:=z.1) cut v vc‖≤w.across ∧
  (∀i∈Finset.Ico v c,‖feeAt R z.1 z.2 v M i‖≤w.coarse i) ∧
  ‖reading R (N:=z.1) floor v le_rfl-I‖≤w.terminal

theorem existing (s:Fin n → Cover)(I:ℂ)(w:Invoice):
    Heard (f:=f) file uv vc ck jK arms s (fun _=>I) w ↔
      ∀ᶠ z:ℕ×ℕ in f.fuse,∀top:K<z.1,Upper file arms jK uv vc ck s z top w.upper ∧
        Later file arms jK uv vc s z I w:=by
  apply eventually_congr
  filter_upwards [] with z
  apply forall_congr'
  intro ztop
  change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
  tauto

theorem original (o s:Fin n → Cover)(z:ℕ×ℕ)(top:K<z.1)(I:ℂ)(phase:ℝ)(w:Invoice)
    (home:Reached arms jK uv vc ck o s phase)
    (upper:Upper file arms jK uv vc ck s z top w.upper)
    (later:Later file arms jK uv vc s z I w):
    let Y:=word R d j z.1 z.2 (jK.trans top.le) o (fun i=>(arms i).source z)
    ‖(C).omega z.1 z.2 Y-I‖≤phase+w.total v c K:=by
  intro Yo
  obtain ⟨ok,fine,across,coarse,bottom⟩:=later
  let col:=fun i=>(arms i).source z
  let Y:=word R d j z.1 z.2 (jK.trans top.le) s col
  let q:=doses R d file.station (N:=z.1) (per:=z.2) (file.A z.1 z.2) col
  let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jK z.2 s
  let bank:=file.row z.1 z.2 q ξ
  have cont:Continuous Y:=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have step:=fixed R uv vc ck top.le Y cont bank ok I
  dsimp only at step
  have inK:entrance R Y (uv.trans (vc.trans ck)) top.le bank≤w.upper:=by
    unfold entrance
    change ‖_-reading R (N:=z.1) (numerator R z.1 z.2 K (file.row z.1 z.2 q ξ K)) u _‖≤w.upper
    rw [file.seed z.1 z.2 top]
    exact upper
  have bill:=step.trans (add_le_add (add_le_add (add_le_add (add_le_add inK
    (sum_le_sum fine)) across) (sum_le_sum coarse)) bottom)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add (home z.1 z.2 top) bill).trans_eq
    (by unfold Invoice.total;ring))

end YM.Integration.WilsonMovingForkFiniteCell
