import YM.Integration.FVA1Physical.Sources.Round2.ScheduledBarePrice
import YM.Integration.FVA1Physical.ExceptionalMass
import YM.Next.MULTISOURCE.GradeHelp

/-! The paid bare-step comparison on entire gauge orbits of weak coarse
fields and its propagation under full measured posterior kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Function Set MeasureTheory Lattice RG YM.Wilson Tree Precision Marker Comparison.RG02
open FVA2.CityHistory FormalOPE.RG10.InversionTop RGComparison.Core16 RGComparison.Core16.Spool
open RGComparison.Core16.Parcel.Oven PertExtension.Series.Tested Pert.Asymptotics PhysicalNext.Repeat.Legato
open YM.Integration.FVA1Physical.Wilson MergeProof.Accent
open scoped Classical Topology BigOperators
variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (R : Census I)
variable (A : Run G) {m p d : ℕ} (U : I → Stamp.Reservation A.family (A.family.side (m+1) p) d) (s : R.Mode)
local notation "S" => A.family.path.levels.clock.op m p
local notation "J" => modeLamp R U A.makes (Next.Foundations.valuation G) s
local notation "pos" => modeSite R U s

/-- The actual normalized mixed physical reading at any retained configuration. -/
def bareReadingAt (g : ℝ) (V : Config G (A.family.side m p)) : ℂ :=
  let β:=g⁻¹^2
  g⁻¹^(power J) • (((S).push β (bare β) V)⁻¹ • (S).push β (fun u=>bare β u • column J pos u) V)

omit [Fintype I] in
theorem bareReading_invariant (g : ℝ) : GaugeInvariant (bareReadingAt R A U s g) := by
  let β:=g⁻¹^2
  let F:=fun u:Config G (A.family.side (m+1) p)=>bare β u • column J pos u
  have fc : Continuous F := (bare_cont β).smul (tally_cont J pos)
  have fi : GaugeInvariant F := by
    intro k u
    change bare β (gauge k u) • tally J pos (gauge k u) = bare β u • tally J pos u
    rw [bare_gauge β u k,tally_invariant J pos k u]
  have den:=Multi.Step.push_gauge A.family.path.levels m p (bare β) (bare_integrable β) (fun k u=>bare_gauge β u k) β
  have num:=Multi.Step.push_gauge A.family.path.levels m p F (fc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fi β
  intro k u
  change g⁻¹^(power J) • (((S).push β (bare β) (gauge k u))⁻¹ • (S).push β F (gauge k u))=_
  rw [den k u,num k u]
  rfl

/-- The paid polynomial approximates the physical reading at every gauge
representative of the same weak field. -/
theorem paid_orbit {r : ℕ} {Q η : ℝ} (paid : PaidBare R A d r Q η)
    (room : Bid.Larger (G:=G) S) (a : I → CoverLabel G d) (y : I → Site (A.family.side (m+1) p))
    (F : Forest (S).ratio) (t : (S).Choices) (L : Bulk.Chain A.family.path)
    (u : Pins G (A.family.side m p)) (weak : ∀ e, ‖u e‖ ≤ Q) (k : Site (A.family.side m p) → G.El) :
    let g:=regulatorRun A.family (m+1) p (m+1)
    let x:=axesP G _ u; let W:=placeLabels (C:=A.family) a y
    let v:=fun i=>(MSMatch.SourceTop.datum R m p W F t x).ordinaryCoefficient L r i s
    ‖bareReadingAt R A W s g (gauge k (slice u g)) - peval v r g‖ ≤ g^((r:ℝ)+1-η) := by
  intro g x W v
  rw [bareReading_invariant R A W s g k (slice u g)]
  have hp:=paid m p room a s y F t u L weak
  change ‖(MSMatch.SourceTop.torusVacuum (C:=A.family) m p (axesP G _ u) g)⁻¹ • MSMatch.SourceTop.torusFull m p W (axesP G _ u) s.val g - peval v r g‖ ≤ g^((r:ℝ)+1-η) at hp
  rw [sourceRatio_eq_reads R W A.makes (Next.Foundations.valuation G) u s g] at hp
  exact hp

/-- With its *current, inherited* vacuum, every subsequent physical RG
kernel is a contraction, through any number of steps. -/
theorem inherited_seed_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : History G) (physical : H.Selected) (N p j : ℕ) (hj : j ≤ N)
    (Y : Config G (H.S.side j p) → E) (C : ℝ) (hY : ∀ v, ‖Y v‖ ≤ C)
    (i : ℕ) (hi : i ≤ j) (V : Config G (H.S.side i p)) :
    ‖((H.rep N p i).eval V)⁻¹ •
      gust H N p j (fun v=>(H.rep N p j).eval v • Y v) i hi V‖ ≤ C := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [gust_base,inv_smul_smul₀ (SectorNext.Vacuum.strictly H physical N p j hj V).ne']
    exact hY V
  | of_succ k hk ih =>
    have hk' : k<N:=lt_of_lt_of_le hk hj
    rw [gust_step H N p j _ hk,←conditionalPush_normalized H physical N p k hk']
    exact conditionalPush_bound H physical N p k hk' _ _ ih V

/-- Replace the measured marked output by its independently computed Wilson
polynomial on the gauge-saturated weak sector. The entire signed discrepancy
there can be propagated to every subsequent scale, all output fields and
all remaining forced sectors with a single physical denominator at each step. -/
theorem paid_orbit_propagates {r : ℕ} {Q η : ℝ} (paid : PaidBare R A d r Q η)
    (room : Bid.Larger (G:=G) S) (a : I → CoverLabel G d) (y : I → Site (A.family.side (m+1) p))
    (F : Forest (S).ratio) (t : (S).Choices) (L : Bulk.Chain A.family.path)
    (good : Set (Config G (A.family.side m p))) (J₀ : Config G (A.family.side m p) → ℂ)
    (hb : ∀ v∈good, ‖J₀ v‖ ≤ 1)
    (coordinates : Config G (A.family.side m p) → Pins G (A.family.side m p))
    (frame : Config G (A.family.side m p) → Site (A.family.side m p) → G.El)
    (hw : ∀ v∈good, ∀ e, ‖coordinates v e‖ ≤ Q)
    (he : ∀ v∈good, gauge (frame v) (slice (coordinates v) (regulatorRun A.family (m+1) p (m+1))) = v)
    (i : ℕ) (hi : i ≤ m) (V : Config G (A.family.side i p)) :
    let g:=regulatorRun A.family (m+1) p (m+1)
    let W:=placeLabels (C:=A.family) a y; let H:=A.family.path
    let bank:=fun v k=>(MSMatch.SourceTop.datum R m p W F t (axesP G _ (coordinates v))).ordinaryCoefficient L r k s
    let diff:=good.indicator (fun v=>J₀ v*(bareReadingAt R A W s g v - peval (bank v) r g))
    ‖((H.rep (m+1) p i).eval V)⁻¹ •
      gust H (m+1) p m (fun v=>(H.rep (m+1) p m).eval v • diff v) i hi V‖ ≤ g^((r:ℝ)+1-η) := by
  intro g W H bank diff
  apply inherited_seed_bound H A.makes.wilson (m+1) p m (Nat.le_succ m) diff _ _ i hi V
  intro v
  by_cases hv : v∈good
  · have approx:=paid_orbit R A s paid room a y F t L (coordinates v) (hw v hv) (frame v)
    change ‖bareReadingAt R A W s g (gauge (frame v) (slice (coordinates v) g)) - peval (bank v) r g‖ ≤ g^((r:ℝ)+1-η) at approx
    rw [he v hv] at approx
    change ‖good.indicator _ v‖≤_
    rw [Set.indicator_of_mem hv,norm_mul]
    simpa only [one_mul] using mul_le_mul (hb v hv) approx (norm_nonneg _) zero_le_one
  · rw [show diff v=0 from Set.indicator_of_notMem hv _,norm_zero]
    exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _

end YM.Integration.FVA1Physical.Round2.Curvature
