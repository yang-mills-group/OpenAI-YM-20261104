import YM.Integration.FVA1Physical.Marked.ShortWallet
import YM.Integration.FVA1Physical.Marked.MixedOwners

/-! A nonempty packet of marked, failed source factors can be charged to a
single actual vacuum owner. The cost records the geometry of the union of
the source supports. It does not grow with the ambient period for fixed
local geometry and uses just one factor of the physical vacuum activity. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Pressure Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset Finset
open scoped Classical BigOperators
variable {G : Gauge} {c : Side} {M Ω : Type} [Fintype M]

def failedProduct (P : Rep G c) (S : M → Support c)
    (F : Ω → M → Config G c → ℝ) (u : Ω) (U : Config G c) : ℝ :=
  ∏ j, maskFailure P.p (S j) (F u j) U

def MixedPrice (P : Rep G c) (S : M → Support c)
    (F : Ω → M → Config G c → ℝ) (C : M → ℝ) (κ : ℝ) : Prop :=
  let H := univ.biUnion S
  let Z := failedProduct P S F
  (∀ u rows U, P.activities.gasOccurrence P.p rows U * Z u U =
    if P.activities.admissible P.p U rows then
      ∑ i ∈ rows, (flagShare P H i U * P.activities.K i U * Z u U) *
        ∏ j ∈ rows.erase i, P.activities.K j U else 0) ∧
  ∃ bound : ℕ → ℝ, (∀ i, 0 ≤ bound i) ∧
    (∀ u i U, |flagShare P H i U * P.activities.K i U * Z u U| ≤ bound i) ∧
    SumBudget (fun i => P.p.mass (H ∪ (P.activities.forced i).support) (bound i))
      ((∏ j, C j)*Real.exp (P.p.supportExponent*coverNumber P.p.B H)*((H.card : ℝ)*κ))

theorem mixed_price [Nonempty M] (P : Rep G c) (S : M → Support c)
    (F : Ω → M → Config G c → ℝ) (C : M → ℝ) {κ : ℝ} (Cpos : ∀ j, 0 ≤ C j)
    (hF : ∀ u j U, |F u j U| ≤ C j) (hK : P.activities.KBound P.p κ) :
    MixedPrice P S F C κ := by
  let H : Support c := univ.biUnion S
  let Z := failedProduct P S F
  have masks (u : Ω) (U : Config G c) : maskFailure P.p H (Z u) U = Z u U := by
    unfold maskFailure
    split
    next clean =>
      let j : M := Classical.choice ‹Nonempty M›
      have hj : Healthy P.p.threshold (S j) U :=
        Finset.disjoint_of_subset_left (subset_biUnion_of_mem S (mem_univ j)) clean
      exact (prod_eq_zero (i := j) (mem_univ j) (show maskFailure P.p (S j) (F u j) U = 0 from if_pos hj)).symm
    next _ => rfl
  constructor
  · intro u rows U
    exact (congr_arg (P.activities.gasOccurrence P.p rows U * ·) (masks u U)).symm.trans
      (failed_occurrence P H (Z u) rows U)
  · apply failed_source_budget P H Z (prod_nonneg (fun j _ => Cpos j)) _ hK
    intro u U
    change |∏ j, maskFailure P.p (S j) (F u j) U| ≤ _
    rw [abs_prod]
    apply prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => ?_)
    unfold maskFailure
    split <;> first | simpa only [abs_zero] using Cpos j | exact hF u j U

variable {V : Type} [DecidableEq V] {B : Census V} {ξ : V → ℕ} {qd b : ℕ}
    {o : V → Site c} {P : Rep G c}

theorem inherited_mixed_price [Nonempty M] (W : Rooms.Wallet Ω o P B ξ qd b) (modes : M → Senses B)
    {O : V → Support c} {price : Parabola.Ray B} {width β allowance κ : ℝ}
    (hw : W.Usable O price width β allowance) (hp : 0 < width) (hK : P.activities.KBound P.p κ) (g : ℝ) :
    MixedPrice P (fun j => Tale.court P.p.B (o (Sonnet.root (modes j))))
      (fun u j => shortValue W (modes j) (Stores.till β) g u)
      (fun j => (price (modes j).val)⁻¹ * valueInvoice G ξ qd b (modes j) g) κ := by
  apply mixed_price _ _ _ _ _ _ hK
  · intro j
    exact mul_nonneg (inv_nonneg.mpr (hw.rental.pos _).le)
      (sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..))
  · intro u j U
    let s := modes j
    let A := Stanza.son (W.prediction u) b
    have weight : |W.weight u s| ≤ (price s.val)⁻¹ :=
      ((le_inv_mul_iff₀ (hw.rental.pos _)).mpr (hw.starts u s)).trans_eq (mul_one _)
    unfold shortValue
    rw [abs_mul]
    exact mul_le_mul weight (wake_bound A s _ (hw.optics u) hp g U) (abs_nonneg _)
      (inv_nonneg.mpr (hw.rental.pos _).le)

end YM.Integration.FVA1Physical.Marked
