import YM.Integration.WilsonPositionProgramNormalizedFieldPurchase
import YM.Integration.WilsonPositionProgramInversionWindowCost

/-! All incoming normalization coefficients, with their actual child tests,
are paid by a fixed inverse power of the one inversion spacing. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramDelayedFieldSale
open Function Finset Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels PowerSeries
open WilsonPositionProgramInversionMaterial
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {a h D k u e : ℕ}

theorem original (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ cost : ℕ, ∀ (D₀ : XSpace.Run) {s : ℕ} (B : WilsonPositionProgramReporterBand.Band R D₀ s),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t : ℕ in atTop,
        let m := B.reporter+t
        let M := m+B.upper t
        let ε := (D₀.step (B.index t)).spacing
        ∀ (X : Herit Q) (b : (i : Fin (a+1)) → Volume (d i)),
          let x := fun i => PermuteLens L R.metals.O (Q i) M m (X i)
          let w := fun i => steep L R.metals.O (Q i).ans (Q i).path M m (M-m) (x i)
          ∀ α : Axes R l, ∀ r≤e, ‖coeff r (dose R l w d admit b α)‖ ≤
            K * ε⁻¹^cost *
              ∏ i, WilsonPositionProgramNormalizedMaster.fee X e i * ‖jewelBloom (admit i) (α i) (b i)‖ := by
  classical
  intro Q L
  obtain ⟨C,E,fields⟩ := WilsonPositionProgramNormalizedFieldPurchase.original R simple v funded p rails l d admit cap
  let loss := fun i => (C i).d+(E i).d
  refine ⟨∑ i,loss i,?_⟩
  intro D₀ s B
  choose U positive paid using fun i => WilsonPositionProgramInversionWindowCost.original R D₀ simple B (C i) (E i)
  obtain ⟨j,starts⟩ := eventually_atTop.mp fields
  let A : ℝ := ((e+1:ℕ):ℝ)^Fintype.card (Fin (a+1))
  have A0 : 0≤A := by positivity
  refine ⟨A * ∏ i,U i, mul_nonneg A0 (Finset.prod_nonneg fun i _ => positive i),?_⟩
  filter_upwards [eventually_ge_atTop j, Filter.eventually_all.mpr paid,
    WilsonPositionProgramInversionWindowCost.bounds R D₀ simple B] with t jt costs bounds
  intro m M ε X b x w α r hr
  have fs := starts j le_rfl m M (le_trans jt (Nat.le_add_left ..)) (Nat.le_add_right ..) X b α r hr
  let f := WilsonPositionProgramNormalizedMaster.fee X e
  let price := fun i => f i * ‖jewelBloom (admit i) (α i) (b i)‖
  have fp i : 0≤f i := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have pp i : 0≤price i := mul_nonneg (fp i) (norm_nonneg _)
  let c := fun i => (C i).buy (Compar L.S (zz L) m M)
  let h' := fun i => (E i).buy (zz L m)
  have cp i : 0≤c i := mul_nonneg ((zero_le_one).trans (C i).good) (pow_nonneg bounds.2.2.1 _)
  have hp i : 0≤h' i := mul_nonneg ((zero_le_one).trans (E i).good) (pow_nonneg bounds.1 _)
  have each i : (c i*(h' i*f i))*‖jewelBloom (admit i) (α i) (b i)‖ ≤
      (U i*ε⁻¹^(loss i))*price i := by
    calc
      _ = (c i * h' i) * price i := by dsimp only [price]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (costs i) (pp i)
  have muls := Finset.prod_le_prod (s:=Finset.univ)
    (fun i _ => mul_nonneg (mul_nonneg (cp i) (mul_nonneg (hp i) (fp i))) (norm_nonneg _))
    (fun i _ => each i)
  refine fs.trans ((mul_le_mul_of_nonneg_left muls A0).trans_eq ?_)
  change A*(∏ i, (U i * ε⁻¹^loss i) * price i)=(A*∏i,U i)*ε⁻¹^(∑ i,loss i)*∏i,price i
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

end YM.Integration.WilsonPositionProgramDelayedFieldSale
end
