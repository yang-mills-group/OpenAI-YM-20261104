import YM.Integration.WilsonRootedOPEPriceChange

/-! Both original phase pages retain their native hats, sites and complete branch weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPhase
open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open MergeProof MergeProof.Accent MergeProof.Replicums MergeProof.Ribbon
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open Extra.Trajectories Push.GridApprox.Nil
open scoped Classical BigOperators
variable {V W : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

def wallet (γ : W→ℂ) : ℝ := (1+∑s,‖γ s‖)^Fintype.card W

omit [Fintype V] in
theorem original (f : W→V) (γ : W→ℂ) (s : (Stock.census W).Mode) :
    ‖QlocalPageAggregation.weight f γ s‖≤wallet γ := by
  have base : 1≤1+∑j,‖γ j‖ := le_add_of_nonneg_right (sum_nonneg fun _ _=>norm_nonneg _)
  unfold QlocalPageAggregation.weight
  split
  · rw [norm_prod]
    apply le_trans _ (pow_le_pow_right₀ base (card_le_univ s.val))
    rw [←Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
    intro i _
    exact (Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset W))=>norm_nonneg (γ j)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  · rw [norm_zero];exact pow_nonneg (zero_le_one.trans base) _

variable {G : Gauge} {n : Side} {P : Rep G n} {Γ : Census V} {I : Type} [Fintype I]

def reprice (q : I→Menu.Hat Γ P) (a : I→ℂ) (i : I) : Menu.Hat Γ P :=
  {q i with charge := (q i).charge*a i}

omit [Fintype V] in
theorem offered (q : I→Menu.Hat Γ P) (a : I→ℂ) (o : V→Site n) (w : V→ℝ) (hw : ∀v,0<w v)
    (B : ℕ) (σ b h : ℝ) (hh : 0≤h) (hread : ∀i,‖a i‖≤h) (safe : Menu.Offer o q w B σ b) :
    Menu.Offer o (reprice q a) w B σ (h*b) := by
  refine ⟨safe.sites, WilsonRootedOPEPriceChange.scaled _ _ _ _ _ _ h hh (fun _=>Menu.Crew w hw) ?_ safe.budget⟩
  intro i
  calc Menu.fare (reprice q a i) w = ‖a i‖*Menu.fare (q i) w := by simp only [reprice,Menu.fare,Menu.sumFee,norm_mul];ring
       _ ≤ h*Menu.fare (q i) w := mul_le_mul_of_nonneg_right (hread i) (Menu.Crew w hw)

end YM.Integration.WilsonRootedOPEPhase
