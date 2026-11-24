import YM.Integration.WilsonAddressedCollarPrice
import YM.Integration.WilsonAddressedCollarFolds

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedThermometerBasis
open Function Filter MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOffsetLedger
open WilsonAddressedReportedColumns WilsonInvariantActionPosition WilsonPositionThermometerGradedSource
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
abbrev degree (i : Fin 3) : ℕ := (grade i).val

/-- The unit has a separate entry at every test letter. -/
abbrev Entry (C : Family G) (d : ℕ) := Letter d ⊕ Mark C d

def coefficient {C : Family G} {d : ℕ} (θ : ℝ) (x : Palette C d) : Entry C d → ℂ :=
  Sum.elim (fun t=>x t 0) (val (weightsAt θ x))

private theorem unitBill {C : Family G} {d : ℕ} (x : Palette C d) :
    (∑ t : Letter d,‖x t 0‖) ≤ size x := by
  rw [bill_group]
  apply Finset.sum_le_sum
  intro t _
  exact Finset.single_le_sum (f:=fun i=>‖x t i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ 0)

theorem bill {C : Family G} {d : ℕ} (θ : ℝ) (x : Palette C d) :
    (∑ i : Entry C d,‖coefficient θ x i‖) ≤ size x + size (weightsAt θ x) := by
  rw [Fintype.sum_sum_type]
  exact add_le_add_left (unitBill x) _

def fee (t m d : ℕ) : ℝ :=
  let k := 5+G.slopeConstant*((t:ℝ)+1)
  k*(β m)^2 + k^(toll R.family d+1)*(β m)^(toll R.family d+2)

abbrev Slots (R : Run G) (I : Finset (Fin 3)) :=
  (i : I) → Entry R.family (degree i.val)

def signed (I : Finset (Fin 3)) (θ : ℝ) (x : (i:Fin 3)→Palette R.family (degree i)) (a : Slots R I) :=
  ∏ i:I,coefficient θ (x i) (a i)

private theorem sums (I : Finset (Fin 3)) (θ : ℝ) (x : (i:Fin 3)→Palette R.family (degree i)) :
    (∑ a : Slots R I,‖signed R I θ x a‖) =
      ∏ i:I,∑ b:Entry R.family (degree i),‖coefficient θ (x i) b‖ := by
  simp only [signed,norm_prod]
  rw [Finset.prod_univ_sum,Fintype.piFinset_univ]

/-- The same three original enrolled physical inputs and one print per child give
    the signed coefficient bills of all proper and full faces simultaneously. -/
theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (t : ℕ) :
    ∀ᶠ m in atTop,∀ N p (_live : m≤N) (z : Fin 3→Site (R.family.side N p)),
      ∃ (V : (i:Fin 3)→Sight R.family (degree i) p) (r : (i:Fin 3)→Emblems R.family (degree i)),
        (∀i,Enrolled R.makes R.doors (cash R) m N p (degree i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (y : (i:Fin 3)→Palette R.family (degree i)) j (away : m≤j) (_reached : j≤N), j≤berth R t m →
          let P := R.family.path.rep N p j
          let v := fun i=>finer (r i) away (y i)
          ∃ x : (i:Fin 3)→Palette R.family (degree i),
            (∀ i,Printed R.family (degree i) P 0 (kappa R.family.path j) (V i j (v i)) (x i) (v i)
              (cash R (degree i) j*size (v i))) ∧
            ∀ I : Finset (Fin 3),(∑ a:Slots R I,‖signed R I P.p.threshold x a‖) ≤
              ∏ i:I,fee R t m (degree i)*size (y i) := by
  let good (m : ℕ) (d : ℕ) := ∀ N p (_live : m≤N) (z : Site (R.family.side N p)),
    ∃ (V : Sight R.family d p) (r : Emblems R.family d),
      Enrolled R.makes R.doors (cash R) m N p d (digits R N p z) V r ∧
      ∀ (y : Palette R.family d) j (away : m≤j) (_reached : j≤N), j≤berth R t m →
        let P := R.family.path.rep N p j
        let v := finer r away y
        ∃ x : Palette R.family d, Printed R.family d P 0 (kappa R.family.path j) (V j v) x v (cash R d j*size v) ∧
          (∑ i : Entry R.family d,‖coefficient P.p.threshold x i‖) ≤ fee R t m d*size y
  have earned (q : ℕ) : ∀ᶠ m in atTop, good m q := by
    filter_upwards [WilsonAddressedCollarPrice.original R simple slow shop q t] with m cohort N p live z
    obtain ⟨V,r,L,course⟩ := cohort N p live z
    refine ⟨V,r,L,?_⟩
    intro y j away reached close P v
    obtain ⟨x,hx,units,rows⟩ := course y j away reached close
    refine ⟨x,hx,(bill _ _).trans ?_⟩
    simpa only [fee,add_mul] using add_le_add units rows
  filter_upwards [(Filter.eventually_all).mpr (fun i:Fin 3 => earned (degree i))] with m all N p live z
  choose V r laws paid using fun i:Fin 3 => all i N p live (z i)
  refine ⟨V,r,laws,?_⟩
  intro y j away reached close P v
  choose x printed bound using fun i => paid i (y i) j away reached close
  refine ⟨x,printed,?_⟩
  intro I
  rw [sums]
  exact Finset.prod_le_prod (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
    (fun i _=>bound i)

end YM.Integration.WilsonAddressedThermometerBasis
