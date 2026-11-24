import YM.Integration.WilsonReflectedPhysicalFiling
import YM.Integration.WilsonCapturedPrimaryCenteredMeter

/-! The filed positive-horizon counterterm on every admitted compact cell
of the physical test, with all original charges and one common reflected center. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryReflectedFunds
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonReflectedPhysicalFiling (Arms reading)
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {n:ℕ} [NeZero n]
local notation "CF" => R.family
local notation "XA" => bling R.alloy.B.a
local notation "origin" z:max axis:max => WilsonCapturedPrimaryPhysicalArray.registered z (some axis)

include simple book in
/-- A complete originally enrolled source at the submitted sites receives its
true finite filing. The capital, submitted-price and terminal weight precede
every cutoff, period, nonzero cell, enrolled arm, and choice of representative. -/
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (slow:WilsonWindowReportingPace.Slow R.kit) (D v h J u:ℕ) (wide:4<v)
    (station:∀p,Opened (CF) h u p) (tiling:Stock.Tabs.opens (CF).path.levels 1 J u) (φ:Test n) :
    ∃ Z:ℝ→ℝ,RateIs trail LogV Z 0 ∧
      RateIs trail LogV (fun r=>terminalCost (CF) h (capture R r) (Z r)) (-(h:ℝ)) ∧ ∀ᶠ r in trail,
    let m:=capture R r
    let k:=launch R simple v r
    ∃(um:u ≤ m) (mk:m+1 < k),∀(N p:ℕ) (kn:k < N) (z:Fin n→Site ((CF).side N p)),
      WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 → ∀i₀:Fin n,
      ∀a:Arms R (Fin n) D N p k,a.sites=(origin z i₀) →
      ∃(q:store (CF) h p m) (x:(CF).label h),
        Funds (CF) R.makes p N m h J u (terminalCost (CF) h m (Z r))
          ((CF).S.a (m+1)^h*(XA m*(4*(1/Z r))))
          (Real.exp (((h:ℝ)+1/16)*LogV r)) (reading R a kn.le) tiling.1 um
          (m.le_succ.trans (mk.le.trans kn.le)) (station p) x q :=by
  obtain ⟨Z,hz,hs,funded⟩:=WilsonReflectedPhysicalFiling.original (I:=Fin n) R simple book shop slow
    D v h J u (by omega) station tiling
  refine ⟨Z,hz,hs,?_⟩
  filter_upwards [funded,WilsonCapturedPrimaryPhysicalArray.original R simple slow J v wide φ,
    WilsonCapturedPrimaryPhysicalChamber.original R J φ,Ioc_mem_nhdsGT ((CF).S.a_pos 1)] with r certified geom central radius
  let b:=WilsonCapturedPrimarySupportedHalo.date R r
  let m:=capture R r
  let k:=launch R simple v r
  have late:1 ≤ b :=by
    have valid:=radius.2.trans ((CF).S.strictAnti.antitone (Nat.zero_le 1))
    have fine:=(WilsonCloseCaptureDate.bracket (CF).S radius.1 valid).1
    by_contra! early
    exact (not_lt_of_ge ((CF).S.strictAnti.antitone (Nat.succ_le_of_lt early))) (fine.trans_le radius.2)
  have step:m+1=b:=Nat.sub_add_cancel late
  have mk:m+1<k:=step ▸ geom.2.1
  obtain ⟨um,file⟩:=certified
  refine ⟨um,mk,?_⟩
  intro N p kn z nonzero i₀ a position
  have bn:b ≤ N :=(geom.2.1.le.trans kn.le)
  have seats:=geom.2.2 N p kn.le z nonzero (some i₀)
  dsimp only at seats
  apply file N p kn mk.le a i₀
  · rw [position]
    exact central N p bn z nonzero (some i₀)
  · rw [position,step]
    change WilsonThermometerOwnOffsetNectar.location R (z i₀-z i₀) b=0
    simp only [sub_self,WilsonThermometerOwnOffsetNectar.location,dif_pos bn,
      WilsonThermometerOwnOffsetTale.site,WilsonCapturedPrimarySubcellOrigin.origin]
  · rw [position,step]
    exact seats.2.2.2.1
  · rw [position]
    exact seats.2.2.2.2.2
  · rw [position,step]
    exact fun i=>seats.2.2.1 i.1 i₀ i.2

end YM.Integration.WilsonCapturedPrimaryReflectedFunds
