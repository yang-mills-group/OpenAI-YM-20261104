import YM.Integration.WilsonIndependentCollarPrintIncome

/-! Read the first occupied Wick rung of the actual marked successor. All
proper splits are retained, as is the pre-existing whole face. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarFirstRung
open Filter Finset Function Lattice Laurent Bloch Metric Precision RG Next.Free Work.F08 Wilson FormalBulk08 Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {G : Gauge} {I : Arch G} {e : ℕ} {ι : Type} [DecidableEq ι] {D k : ι→ℕ} {Z : Finset ι}

theorem original (p : PackOne Z D k e I) (S : Finset ι) (r : ℕ) :
    p.surfU S 1 0 r = ripple p.N (p.surfU S 0 0) r +
      ∑ T∈S.powerset, if sub:T⊆S then
        ∑ a∈antidiagonal r, refuge (swivel (lakeL p.N sub (p.surfU T 0 0)
            (p.surfU (S\T) 0 0) r a.1 a.2)) else 0 := by
  have live (t : ℕ) : p.V.vault t 0 = 0 := by
    rw [p.V.vaultTip]
    apply bare_abr
    unfold ScrollV.archCold
    rw [pack_zero _ I.pay]
    rfl
  have absent (C : Matrix (Site p.V.n × I.dial) (Site p.V.n × I.dial) ℝ) :
      ravel C p.V.vault (p.surfU S) 0 0=0 := by
    rw [WilsonThermometerUnitFilingWeakOneVertex.positive C p.V.vault (p.surfU S) live]
    simp
  have entry := congrFun (p.more S 0 0) r
  rw [absent p.N,absent p.N.transpose] at entry
  refine entry.trans ?_
  simp only [Nat.zero_add,Nat.cast_one,inv_one,one_smul,add_zero,Pi.add_apply,Finset.sum_apply]
  congr 1
  apply sum_congr rfl; intro T _
  split <;> rename_i sub
  · simpa [sewsV] using (lakeReads p.N sub (p.surfU T 0 0) (p.surfU (S\T) 0 0) r).symm
  · rfl

end YM.Integration.WilsonIndependentCollarFirstRung
