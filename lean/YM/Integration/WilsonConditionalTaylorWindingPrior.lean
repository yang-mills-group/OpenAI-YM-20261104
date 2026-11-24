import YM.Integration.WilsonConditionalTaylorWindingDeposit
import YM.WilsonCoeffUV.Emit.Expense

/-! The actual incoming signed family on the geometric upper branch. Only
forbidden ancestor configurations are removed. Empty, single, and connected
multiple slots use their own authentic original receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWindingPrior
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding PathCost WilsonConditionalTaylorSeparatedPurchase
open scoped Classical BigOperators Topology
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k K:ι→ℕ} {e m N t:ℕ}
variable {Q:Realm G (e+1) Credit.leanC} {W:Credit} {P:Outerm G D} {z ρ:ℝ}

def kept (Q:Realm G (e+1) Credit.leanC) (m t N:ℕ) (ρ:ℝ) (K k:ι→ℕ) (P:Outerm G D):Outerm G D:=
  reserveGood Q.draws.S m (t+1) ρ (Gears Q.draws Q.paid K k N N (t+1) P)

omit [Fintype ι] in
theorem sound (win:Borealis Q D k K P m N W z) (hi:t<N):
    Wellness k (kept Q m t N ρ K k P):=
  reserveSpec _ _ _ _ (Cog Q.draws Q.paid le_rfl P win.head Q.hG Q.green hi)

theorem paid (win:Borealis Q D k K P m N W z) (cl:Cloze D k Q Credit.leanC)
    (gate:galeGate G D k K e W Credit.leanC Credit.leanC z≤ρ) (old:m≤t) (hi:t<N)
    (v:ι→ Cover) (Z:Finset ι):
    let A:=W.buy (z+snowP Q.draws.S m (t+1))
    let I:=(Q.mint t (win.main.trans old)).gear
    Eu k (kept Q m t N ρ K k P v) ∧ kept Q m t N ρ K k P v ∅=0 ∧ safeB v (kept Q m t N ρ K k P v) Z e I.past A:=by
  intro A I
  have health:=sound (ρ:=ρ) win hi
  have original:=Cog Q.draws Q.paid (K':=K) le_rfl P win.head Q.hG Q.green (show t+1≤N from hi)
  have mt:m≤t+1:=by omega
  have hz:1≤z:=(Q.depth _ win.main).trans win.yell
  have hA:1≤A:=W.purchase (hz.trans (le_add_of_nonneg_right (sub_nonneg.mpr (scales Q.draws.S mt))))
  refine ⟨health.level' v,health.quiet' v,?_⟩
  intro S sub i ie r
  apply Wig.shave _ (Q.crossing t (win.main.trans old))
  unfold kept reserveGood
  split
  next clear=>
    by_cases empty:S=∅
    · subst S
      rw [original.quiet' v]
      exact Wig.zero.more (by simp)
    by_cases multiple:1<S.card
    · have strict:=coruscate win cl gate mt hi v clear multiple (a':=ie) (r:=r)
      have one:Real.exp (-penaltyB Credit.leanC z ρ (snowP Q.draws.S m (t+1)))≤1:=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (penaltyBound hz ((gale_nn G D k K e W Credit.leanC Credit.leanC hz).trans gate) _))
      exact strict.more (one.trans (one_le_pow₀ hA))
    · obtain ⟨s,rfl⟩:=Finset.card_eq_one.mp (show S.card=1 by
        have pos:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty);omega)
      exact win.sing (t+1) v mt hi s i ie r
  next=>exact Wig.zero.more (pow_nonneg (zero_le_one.trans hA) _)

omit [Fintype ι] in
theorem agrees (v:ι→ Cover) (S:Finset ι) (ok:cleared Q.draws.S m (t+1) ρ v S):
    kept Q m t N ρ K k P v S=Gears Q.draws Q.paid K k N N (t+1) P v S:=if_pos ok

end YM.Integration.WilsonConditionalTaylorWindingPrior
end

