import YM.Integration.WilsonReflectedPhysicalRate

/-! Fixed real-radius, cutoff-uniform reflected filing of independently
placed original Wilson arms. Observable and counterterm are on the same
positive original law. Both microscopic and macroscopic dates are elected
before the two physical regulator limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPhysicalFiling
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {I:Type} [Fintype I] [DecidableEq I] [Nonempty I]
set_option quotPrecheck false
local notation "C" => R.family
local notation "B" => R.family.path.levels.budget
local notation "X" => bling R.alloy.B.a

structure Arms (I:Type) (D N p k:ℕ) where
  sites : I→Site (R.family.side N p)
  grade : I→ℕ
  limited : ∀i,grade i ≤ D
  viewer : (i:I)→Sight R.family (grade i) p
  sections : (i:I)→Emblems R.family (grade i)
  enrolled : ∀i,WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
    k N p (grade i) (WilsonThermometerOffsetResidue.digits R N p (sites i)) (viewer i) (sections i)
  vector : (i:I)→Palette R.family (grade i)
  bounded : ∀i,size (vector i) ≤ 1

def reading {D N p k:ℕ} (a:Arms R I D N p k) (kn:k ≤ N) : Cut R.family N p :=
  fun U=>∏i,WilsonThermometerIntrinsicRoster.source R a.grade a.sites a.vector a.sections kn i U

omit simple book [Nonempty I] in
theorem inside {D N p k J:ℕ} (a:Arms R I D N p k) (kn:k ≤ N) (jn:J ≤ N)
    (near:∀i,∀v:R.family.label (a.grade i),Interior ((center R.family.S p jn 0).chamber 0)
      (R.family.O N p v (a.sites i))) :
    Interior ((center R.family.S p jn 0).chamber 0) (reading R a kn) :=by
  let cut:= (center R.family.S p jn 0).chamber 0
  let f:=WilsonThermometerIntrinsicRoster.source R a.grade a.sites a.vector a.sections kn
  have each (i:I):Interior cut (f i):= (Interior.constant cut ((R.family.S.a k:ℂ)^(a.grade i))).times (near i _)
  have part (s:Finset I):Interior cut (fun U=>∏i∈s,f i U):=by
    induction s using Finset.induction with
    | empty=>simpa using Interior.constant cut (1:ℂ)
    | insert i s no ih=>simpa only [Finset.prod_insert no] using (each i).times ih
  exact part Finset.univ

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (D v h J u:ℕ) (wide:0<v) (station:∀p,Opened R.family h u p)
    (tiling:Stock.Tabs.opens R.family.path.levels 1 J u) :
    ∃ Z:ℝ→ℝ,RateIs trail LogV Z 0 ∧
      RateIs trail LogV (fun r=>terminalCost R.family h (capture R r) (Z r)) (-(h:ℝ)) ∧
      ∀ᶠ r in trail,
      let m:=capture R r
      let k:=launch R simple v r
      ∃(um:u ≤ m),∀(N p:ℕ) (kn:k < N) (mk:m+1 ≤ k) (a:Arms R I D N p k) (i₀:I),
        (∀i,8*‖R.family.S.place (a.sites i)‖ ≤ R.family.S.a J) →
        WilsonThermometerOwnOffsetNectar.location R (a.sites i₀) (m+1)=0 →
        (∀ i,m+1 ≤ i → i ≤ k → Cross (B i).B (site (J:=J) R a.sites i)) →
        (∀s t,s≠t → (B k).B^2 < separation (site (J:=J) R a.sites k s) (site R a.sites k t)) →
        (∀i:Site (R.family.side J p)×I,coverNumber (B (m+1)).B
          ({site R (J:=J) a.sites (m+1) (i.1,i₀),site R a.sites (m+1) i}:Support _) ≤ 1) →
        ∃(q:store R.family h p m) (x:R.family.label h),
          Funds R.family R.makes p N m h J u (terminalCost R.family h m (Z r))
            (R.family.S.a (m+1)^h*(X m*(4*(1/Z r))))
            (Real.exp (((h:ℝ)+1/16)*LogV r)) (reading R a kn.le) tiling.1 um
            (m.le_succ.trans (mk.trans kn.le)) (station p) x q :=by
  obtain ⟨cap,start⟩:=dates R simple slow v wide
  obtain ⟨Z,hz,hr,purchased⟩:=WilsonReflectedPurchasedFiling.original (I:=I) R simple book shop
    D h u J (station 0).post PhysMS.to_log_zoom cap start
  refine ⟨Z,hz,hr,?_⟩
  have interiorFees:=eventually_all_finset (Finset.range (max D h+1)) |>.mpr
    (fun e _=>near_center R.family J e R.makes)
  obtain ⟨n,late⟩:=eventually_atTop.mp interiorFees
  filter_upwards [purchased,cap.grows.eventually_ge_atTop u,start.grows.eventually_ge_atTop n,
    cap.grows.eventually (plenty R.family.path.levels J (lensScope R.family h))] with r current um enough room
  refine ⟨um,?_⟩
  intro N p kn mk a i₀ near anchor cross spread together
  let mn:=(capture R r).le_succ.trans (mk.trans kn.le)
  let jn:=tiling.1.trans (um.trans mn)
  have fees:=late N (enough.trans kn.le)
  have nearF:=inside R a kn.le jn (fun i=>fees (a.grade i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ((a.limited i).trans (le_max_left ..)))) jn p (a.sites i) (near i))
  have columns (x:R.family.label h):Interior ((center R.family.S p jn 0).chamber 0) (R.family.O N p x 0):=
    fees h (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right ..))) jn p 0 (by rw [latzero];simp [(R.family.S.a_pos J).le]) x
  exact current N p kn mk um (station p) tiling room i₀ a.grade a.limited a.sites a.viewer a.sections a.enrolled
    a.vector a.bounded anchor cross spread together nearF columns
end YM.Integration.WilsonReflectedPhysicalFiling
