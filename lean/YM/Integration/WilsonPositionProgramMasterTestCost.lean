import YM.Integration.WilsonPositionProgramDelayedFieldSale
import YM.Integration.WilsonPositionProgramSeriesRead

/-! A chosen power of the exact inversion spacing pays every coupling
coefficient of the actual upper normalization before the shared inversion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramMasterTestCost
open WilsonPositionProgramSeriesRead
open Function Finset Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels PowerSeries
open WilsonPositionProgramInversionMaterial
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Classical Topology BigOperators ENNReal
variable {G : Gauge} (R : Run G) {a h D k u e : ℕ}

theorem spend {J : Type} [Fintype J] {ε : ℝ} (εpos : 0<ε) (C : ℝ) (h z : ℕ)
    (w : J → ℂ) (v : J→ℝ) (paid : ∀ j, ‖w j‖ ≤ C*ε⁻¹^h*v j) :
    ENNReal.ofReal (ε^(z+h)) * ∑ j, ‖w j‖ₑ ≤ ENNReal.ofReal (C*ε^z*∑ j,v j) := by
  have combine : ∑ j,‖w j‖ ≤ C*ε⁻¹^h*∑ j,v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => paid j
  simp only [←ofReal_norm]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _),←ENNReal.ofReal_mul (pow_nonneg εpos.le _)]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left combine (pow_nonneg εpos.le _)).trans_eq ?_)
  rw [pow_add,inv_pow]
  field_simp

theorem original (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ loss : ℕ, ∀ (D₀ : XSpace.Run) {s : ℕ} (B : WilsonPositionProgramReporterBand.Band R D₀ s),
      ∃ C : ℝ, 0≤C ∧ ∀ᶠ t : ℕ in atTop,
        let m := B.reporter+t
        let M := m+B.upper t
        let ε := (D₀.step (B.index t)).spacing
        ∀ (X : Herit Q) (b : (i : Fin (a+1)) → Volume (d i)),
          let x := fun i => PermuteLens L R.metals.O (Q i) M m (X i)
          let w := fun i => steep L R.metals.O (Q i).ans (Q i).path M m (M-m) (x i)
          let ζ := dose R l w d admit b
          ∀ q≤e, ∀ z : ℕ,
          ENNReal.ofReal (ε^(z+loss)) * ∑ t : Terms R l q, ‖weight R l q ζ t‖ₑ ≤
            ENNReal.ofReal (C*ε^z*∑ t : Terms R l q,
              ∏ i, WilsonPositionProgramNormalizedMaster.fee X e i *
                ‖jewelBloom (admit i) (t.1 i) (b i)‖) := by
  intro Q L
  obtain ⟨loss,sold⟩ := WilsonPositionProgramDelayedFieldSale.original R simple v funded p rails l d admit cap
  refine ⟨loss,?_⟩
  intro D₀ s B
  obtain ⟨C,C0,sales⟩ := sold D₀ B
  refine ⟨C,C0,?_⟩
  filter_upwards [sales] with t reads
  intro m M ε X b x w ζ q hq z
  apply spend (D₀.step (B.index t)).positive C loss z
  intro t'
  have ad := Finset.HasAntidiagonal.mem_antidiagonal.mp t'.2.property
  exact reads X b t'.1 t'.2.val.1 (by omega)

end YM.Integration.WilsonPositionProgramMasterTestCost
end
