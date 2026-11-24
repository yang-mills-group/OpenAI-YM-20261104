import YM.Integration.WilsonCapturedPrimaryReflectedFunds
import YM.Integration.WilsonReflectedPhysicalCounterterm

/-! The signed original product minus its own fixed-u filed counterterm on
the true reflected chamber, with the same capital for every occupied cell. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySpatialFunds
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
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (slow:WilsonWindowReportingPace.Slow R.kit) (D v h J u:ℕ) (wide:4<v)
    (enlarged:(CF).ref h ≤ J) (station:∀p,Opened (CF) h u p) (tiling:Stock.Tabs.opens (CF).path.levels 1 J u) (φ:Test n) :
    ∃ (Z:ℝ→ℝ) (K:ℝ),1 ≤ K ∧ RateIs trail LogV Z 0 ∧
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
          (m.le_succ.trans (mk.le.trans kn.le)) (station p) x q ∧
        let Y:=reading R a kn.le
        let bn:=m.le_succ.trans (mk.le.trans kn.le)
        let filed:=WilsonMacroscopicRichChildRegistration.returned (CF) R.makes (station p) (um.trans bn) Y
        let Q:=Y-(CF).O N p filed 0
        let M:=center (CF).S p (tiling.1.trans (um.trans bn)) 0
        Interior (M.chamber 0) Q ∧ M.rootTest ((CF).beta N p) Q ≤ K*r^((h:ℝ)+1/32) :=by
  obtain ⟨Z,hz,hs,purchase⟩:=WilsonCapturedPrimaryReflectedFunds.original (n:=n) R simple book shop slow
    D v h J u wide station tiling φ
  obtain ⟨K,one,root⟩:=WilsonReflectedPhysicalCounterterm.original R book h J u enlarged station tiling hs
  refine ⟨Z,K,one,hz,hs,?_⟩
  filter_upwards [purchase,root] with r sold original
  obtain ⟨um,mk,issued⟩:=sold
  refine ⟨um,mk,?_⟩
  intro N p kn z paid i₀ a proper
  obtain ⟨q,x,proof⟩:=issued N p kn z paid i₀ a proper
  exact ⟨q,x,proof,original N p um _ _ q x _ proof⟩

end YM.Integration.WilsonCapturedPrimarySpatialFunds
