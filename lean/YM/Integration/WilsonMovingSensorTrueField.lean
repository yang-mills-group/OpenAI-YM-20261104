import YM.Integration.WilsonMovingSensorCircumference
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps

/-! Every sensor enclosing the genuine reporting collar, including every
original catalogue fence, reads the actual folded update to the requested order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorTrueField
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue
open scoped Classical Topology BigOperators

open FullVolume WilsonCoeffUV.Winding
open scoped Classical BigOperators
open Pressure PhysicalNext.Repeat WilsonLimitConstruction WilsonCoeffUV.Embroider
variable {G:Gauge}

/-- The catalogue side always encloses the true logarithmic collar. -/
theorem fence (b:ℝ) (k:ℕ) (i:Slide.Stars) :
    radiusB b ≤ (Trio.fence k (radiusB b) i).val := by
  change radiusB b≤2*((4*_+100*(1+radiusB b))+_)
  omega

/-- One authentic realm at every sufficiently late starting date covers
all subsequent single updates, all larger cutoffs and all independent sensor
circumferences. The full signed polarization is allowed at every geometry. -/
theorem original (R:Run G) (simple:G.Simple) (paid:WilsonMovingSensorReserve.Extra R.kit)
    (e i r H:ℕ) (hi:i≤e) : ∀ᶠ m:ℕ in atTop,
    ∃ Q:Realm G (e+1) Credit.leanC, Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧
      Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      ∀ t, m≤ t → ∀(N:ℕ)(n:Side), t<N →
      radiusB (R.alloy.B.a.clock.hatBeta t)≤n.val →
      ∀ w:stars G r n→ℝ,(∀x,‖w x‖≤1) →
        2*‖∑ x:stars G r n,w x*(lagoon (freshet R.family.path.levels R.metals.O N t i (r+1)) n x-
          coil0 R.family.path.levels R.metals.O t N n i (r+1) x)‖≤(R.alloy.B.a.clock.hatBeta t)^(-(H:ℝ)) := by
  obtain ⟨s,U,pos,finance⟩:=WilsonMovingSensorReserve.original (G:=G) e i r hi
  have hot:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have curve:= hot.eventually (WilsonMovingSensorCircumference.original (G:=G) r H U)
  obtain ⟨beg,guard⟩:=eventually_atTop.mp (curve.and (hot.eventually_gt_atTop 0))
  filter_upwards [finance R simple paid,eventually_ge_atTop beg] with m pm hm
  obtain ⟨Q,here,levels,table,growth,birth,hay⟩:=pm
  refine ⟨Q,levels,table,growth,birth,?_⟩
  intro t mt N n older room w bounded
  let I:=(Q.mint t (here.trans mt)).gear
  have fee:=hay t mt
  have band:=guard t (hm.trans mt)
  let b:=R.alloy.B.a.clock.hatBeta t
  have cover:(Real.log b)^2≤(n.val:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast room)
  have admitted:(perchA (s I) r)⁻¹≤1+Real.log (Real.log b):=by
    have hh:=fee.1;change _≤Credit.leanC.buy (Q.y t) at hh;rw [growth,Credit.lean_cost] at hh;exact hh
  apply fee.2 N n older H b band.2 _ w bounded
  change _+Real.log (2*windPay _ (U.buy (Q.y t)) r)≤_
  rw [growth]
  exact band.1 n cover (pos I) admitted

end YM.Integration.WilsonMovingSensorTrueField
end
