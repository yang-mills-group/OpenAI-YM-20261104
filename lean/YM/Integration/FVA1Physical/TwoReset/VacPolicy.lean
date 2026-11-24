import YM.Integration.FVA1Physical.TwoReset.NextFk

/-! Actual Wilson model vacuum and beta recurrence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Faith QuadraticLocal.Rebirth Comparison.RG02 Comparison.RG02.Bulk
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire AllOrder.Ink AllOrder.Ink.Money
open Laurent Stationary Kinetic.Port Pane Marker Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable {N n i k m : ℕ}
set_option quotPrecheck false
local notation "sz"=> R.family.side
local notation "S" => R.alloy.B.a.S
local notation "op"=> R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "B" y:max => R.alloy.B.kin.path N y
local notation "cl" x:max=> ( R.alloy.B.a.params x ).clip
local notation "T"=> Step.tape ( k+2 )
variable (X Y : ℕ→Layout G) (q q':ℕ→Pace.Coin)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
variable (Z : Step.PlanV.Path D R.alloy Q k N m X q)

-- Claim on the unmasked trajectory (Legato/Burn). No c-dependent
-- allocations, or per-fit, leave top scalar unspecified in the estimates.
structure Prescription (N m k : ℕ):Prop where
  legal : ∀ i:ℕ, m ≤ i→ i ≤ N → Legal (Step.tape (k+2)) (X i)
  top : ∀ l≤ k+2,∀ n:Side,massJets R N N k (X N) l n=PertExtension.Series.Radial.jet (Wilson.energy ∘ Stationary.input G n) (l+2)
  step : ∀ i:ℕ,m ≤ i → ∀ (h:i<N), AffineMass R h (X (i+1)) (X i) (q i) k

include Z
lemma authentic (F:Step.PlanV.Spec D Q R.alloy R.kit)
    (hA:∀ i,m ≤ i→i<N→Bid.Larger (G:=G) (op i n)) : Prescription R X q N m k := by
  refine ⟨fun i hl hh=> ⟨fun j ht=>?_,fun j ht=> (Z.1 i hl hh j ht).symm⟩,fun l hl n=> Step.PlanV.started D R.alloy R.kit Q F X q Z n hl,fun i he hi=>?_⟩
  · exact ⟨_,_,(D.shape k|>.pos _ j),(Z.1 i hl hh j ht).pay⟩
  obtain ⟨C,hx,hZ,hL,hV,he'⟩:= Z.2.2 i he hi; exact calculator R D Q hx C hZ hi _ _ _ (hA i he hi) hL hV he'

-- on supplied run this prescription of mass (couplings AND marked
-- denominator's inherited argument) is unique up to all the probes. Not
-- allowing the all-order step to FIT the next step's answer.
local notation "X₀" z:max i:max => massJets R N i k z
variable (U: Prescription R X q N m k) (H:Prescription R Y q' N m k) (g:G.Simple)
include g U H
lemma every_jet : ∀ i,m≤ i → i≤ N→ ∀ j≤ k+2, massJets R N i k (X i) j = massJets R N i k (Y i) j:= by
   intro i he hv; induction hv using Nat.decreasingInduction with
   | self=> intro j hj; exact funext fun n=> (U.top j hj n).trans (H.top j hj n).symm
   | of_succ i hi ih=>
     have hm:= U.step i he hi
     have ht:= H.step i he hi
     have hz: AffineMass R hi (Y (i+1)) (X i) (q i) k:= mass_same R hi (U.legal (i+1) (by omega) hi) (H.legal _ (by omega) hi) (ih (by omega)) hm
     obtain ⟨C,hx,hC,hK,hV,hB⟩:= Z.2.2 _ he hi; intro j hj; funext n x
     exact Complex.ofReal_injective (neg_injective (congr_fun (jet_unique R D C hC hi _ _ _ _ _ hz ht g hj n) x))
lemma every_unit {i:ℕ}(hi:m ≤ i)(hv:i<N)(j:ℕ)(he:j≤ k+2): q i j=q' i j:=by
   have hx := mass_same R hv (U.legal (i+1) (by omega) hv) (H.legal (i+1) (by omega) hv) (every_jet R X Y q q' D Q Z U H g (i+1) (by omega) hv) (U.step i hi hv)
   obtain ⟨C,hs,ht,-⟩:= Z.2.2 i hi hv; exact backed R D C ht hv _ _ _ _ _ hx (H.step i hi hv) g he
end YM.Integration.FVA1Physical.TwoReset
