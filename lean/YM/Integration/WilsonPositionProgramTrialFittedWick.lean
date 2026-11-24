import YM.Integration.WilsonPositionProgramTrialFittedTable

/-! The complete real Wick matrix of the same elected incoming section before all cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedWick
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedTable (change)
open scoped BigOperators Classical
variable {G:Gauge}

theorem original (H:Hol G)(Q:SealR G)(e:ℕ)(E W B:Credit):
    ∃D:Credit,∀(T:Theatre H Q.ans Q.path e E W),Weston T B → ∀m N:ℕ,T.V.anchor ≤ m → m ≤ N →
      (∀i j,‖Wray T.V.draws T.V.paid Q.ans Q.path N m i j‖≤T.V.cash D m) ∧
      ∀K t i j,‖change T.V.draws T.V.paid Q N m K t i j‖≤
        T.V.cash D m*∑z,‖lineS (CurNames T.V.draws T.V.paid Q.ans Q.path N m (K-m) false) t z j‖:=by
  obtain ⟨D,priced⟩:=tinged H Q.ans Q.path E W B e
  refine ⟨D,?_⟩
  intro T archive m N early long
  have bank(i j):‖Wray T.V.draws T.V.paid Q.ans Q.path N m i j‖≤T.V.cash D m:=
    (priced T archive m m N N early le_rfl long long i j).main
  refine ⟨bank,?_⟩
  intro K t i j
  unfold WilsonPositionProgramTrialFittedTable.change
  rw [Matrix.mul_apply,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum;intro z _
  rw [norm_mul];exact mul_le_mul_of_nonneg_right (bank i z) (norm_nonneg _)

end YM.Integration.WilsonPositionProgramTrialFittedWick
