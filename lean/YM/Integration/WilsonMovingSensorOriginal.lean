import YM.Integration.WilsonMovingSensorBill
import YM.WilsonCoeffUV.Winding.Gazette
import YM.Integration.WilsonMovingLogStation

/-! A purchased original winding update on a submitted finite sensor, folded
from the upper cover action. The positive-valence tests may be fully signed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorOriginal
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue
open scoped Classical Topology BigOperators

open FullVolume WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge}

/-- The width, admission and credit precede the whole model and every site.
The side of the single updated sensor is still independently submitted. -/
theorem quoted (e i r:ℕ) (grade:i≤e) :
    ∃ (s c:Gear G→ℝ) (U:Credit), (∀I,0<s I ∧ (perchA (s I) r)⁻¹≤c I) ∧
    ∀ (R:Run G) (Q:Realm G (e+1) Credit.leanC),
      Q.draws=R.family.path.levels → Q.paid=R.metals.O →
      ∀ (m N:ℕ) (n:Side) (date:Q.anchor ≤ m), m<N →
      let I := (Q.mint m date).gear
      let t := perchA (s I) r
      let A := windPay (s I) (Q.cash U m) r
      c I≤Q.cash Credit.leanC m → ∀ (H:ℕ) (b:ℝ), 0<b →
        (H:ℝ)*Real.log b + (r+1:ℕ)*Real.log (Fintype.card (Co n (Hooks G)):ℝ) +
          Real.log (2*A) ≤ (t/16)*n.val → ∀ w:stars G r n→ℝ, (∀x,‖w x‖≤1) →
        2*‖∑ x:stars G r n,w x*(lagoon (freshet R.family.path.levels R.metals.O N m i (r+1)) n x-
          coil0 R.family.path.levels R.metals.O m N n i (r+1) x)‖≤ b^(-(H:ℝ)) := by
  obtain ⟨s,c,U,hs,take⟩ := purchaseW G e i (r+1) grade Credit.leanC Credit.leanC
    (fun I=>I.past) (fun I=>I.depth)
  refine ⟨s,fun I=>max (c I) ((perchA (s I) r)⁻¹),U,fun I=>⟨(hs I).1,le_max_right ..⟩,?_⟩
  intro R Q levels chart m N n date live I t A reserve H b warm height w bounded
  have walk := ((perch Q.draws Q.paid Q.hG Q.green live).growth i (r+1)).road
  have tensor := costOrbit (take Q m N n date live ((le_max_left ..).trans reserve)) (hs I).1 walk
  have debit : 0 < Q.cash U m := zero_lt_one.trans_le (Credit.purchase U (Q.depth m date))
  have earn : 0<A := by dsimp [A,windPay]; positivity [(hinge_reserve (hs I).1 r)]
  rw [←levels,←chart]
  exact WilsonMovingSensorBill.polarized _ _ (perch_pos (hs I).1 r) earn warm tensor height w bounded

end YM.Integration.WilsonMovingSensorOriginal
end
