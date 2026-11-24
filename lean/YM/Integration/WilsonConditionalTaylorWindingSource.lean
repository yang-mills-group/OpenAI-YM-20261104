import YM.Integration.WilsonConditionalTaylorWindingDeposit

/-! Unscaled genuine source coefficients are paid before the positions and
the upper endpoint, using their finite sums over the original physical
basis. This buys the native single-slot and signed multiple-slot income. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWindingSource
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonConditionalTaylorSeparatedPurchase
open scoped Classical BigOperators Topology
variable {G:Gauge} {n e:ℕ}

def sourceLoad (Q:Realm G (e+1) Credit.leanC) (m:ℕ) (T:Fin n→SealR G) (X:(i:Fin n)→ Verse (T i).F):ℝ:=
  Q.y m+∑i,fee (T i) (X i) e

def charge (T:Fin n→SealR G) (e:ℕ):Credit :=
  (dictated (hol G) T Credit.leanC Credit.leanC Credit.leanC Credit.leanC e).choose

theorem earned (Q:Realm G (e+1) Credit.leanC) (m N:ℕ) (here:Q.anchor≤ m) (upper:m≤N) (T:Fin n→SealR G) (X:(i:Fin n)→ Verse (T i).F)
    (wallet:Tribe Q (hol G) Credit.leanC Credit.leanC T):
    Borealis Q (fun i=>(T i).D) (fun i=>(T i).h) (fun i=>(T i).h) (coatA Q.draws Q.paid N m T X) m N
      (charge T e) (sourceLoad Q m T X):=by
  apply (dictated (hol G) T Credit.leanC Credit.leanC Credit.leanC Credit.leanC e).choose_spec Q wallet m N X _ here upper
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>(fee_pos _ _ _).le)
  · intro i j hj a
    have reported:=funded (T i) (X i) e 1 le_rfl j hj a
    rw [Credit.lean_cost,mul_one] at reported
    have belongs:=Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>fee (T i) (X i) e) (fun i _=>(fee_pos _ _ _).le) (Finset.mem_univ i)
    rw [Credit.lean_cost]
    exact reported.trans (belongs.trans (le_add_of_nonneg_left (zero_le_one.trans (Q.depth m here))))

end YM.Integration.WilsonConditionalTaylorWindingSource
end

