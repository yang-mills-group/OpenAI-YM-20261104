import YM.Integration.WilsonMovingForkHeterogeneousCut

/-! Every one of the two moving readings can be settled at the actual optical trial
against its own cutoff-dependent numerical output, before taking limits. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkDatedExterior
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
open WilsonMovingForkHeterogeneousCut (Filed Invoice)
variable {G:Gauge}{R:Run G}{n:ℕ}{d:Fin n → ℕ}{K:ℕ}(b:Filed R d K)
    {u v c j:ℕ}
local notation "C" => R.family
def At (uv:u≤v)(vc:v≤c)(ck:c≤K)(jK:j≤K)(o:Fin n → Cover)
    (z:ℕ×ℕ)(top:K<z.1)(input:∀i,(C).label (d i))(terminal:ℂ)(w:Invoice):Prop:=
    let a:=input
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
    ‖reading R (N:=z.1) bottom v le_rfl-terminal‖ ≤ w.terminal

/-- Only the unrestricted microscopic reading is translated. All later fares
are on the conditional with its actual pins and the pre-elected A inverse. -/
theorem original (uv:u≤v)(vc:v≤c)(ck:c≤K)(jK:j≤K)(actual offered:Fin n → Cover)
    (z:ℕ×ℕ)(top:K<z.1)(input:∀i,(C).label (d i))(terminal:ℂ)(w:Invoice)(phase:ℝ)
    (paid:At b uv vc ck jK offered z top input terminal w)
    (placed:‖(C).omega z.1 z.2 (word R d j z.1 z.2 (jK.trans top.le) actual input)-
      reading R (N:=z.1) (credit C z.1 z.2 0 (word R d j z.1 z.2 (jK.trans top.le) offered input)
        u ((uv.trans (vc.trans ck)).trans top.le)) u le_rfl‖≤phase):
    ‖(C).omega z.1 z.2 (word R d j z.1 z.2 (jK.trans top.le) actual input)-terminal‖≤
      phase+w.total v c K:=by
  let Y:=word R d j z.1 z.2 (jK.trans top.le) offered input
  let q:=doses R d b.station (N:=z.1) (per:=z.2) (b.A z.1 z.2) input
  let ξ:=seats (R:=R) jK z.2 offered
  let M:=b.row z.1 z.2 q ξ
  obtain ⟨wage,entry,old,capture,young,last⟩:=paid
  have cont:Continuous Y:=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have first:entrance R Y (uv.trans (vc.trans ck)) top.le M≤w.upper:=by
    unfold entrance
    change ‖_ - reading R (N:=z.1) (numerator R z.1 z.2 K (b.row z.1 z.2 q ξ K))
      u (uv.trans (vc.trans ck))‖≤_
    rw [b.seed z.1 z.2 top q ξ]
    exact entry
  have hearing:=WilsonPublicForkTrialHearing.fixed R uv vc ck top.le Y cont M wage terminal
  dsimp only at hearing
  have full:=hearing.trans (add_le_add (add_le_add (add_le_add (add_le_add first
    (sum_le_sum old)) capture) (sum_le_sum young)) last)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add placed full).trans_eq (by
    unfold Invoice.total;ring))

end YM.Integration.WilsonMovingForkDatedExterior
end
