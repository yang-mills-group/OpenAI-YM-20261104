import YM.Integration.ManuscriptQLocalHealthyRate
import YM.MergeProof.Fruit

/-! Actual fine coupling radii and temporary independent marker radii before
the signed local cluster integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkerReserve
open Filter Finset Lattice RG Wilson Marker MergeProof Push.AbsoluteSums
open RG3.Forms RG3.Script.Picnic LocalComparison FullQLocal FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical Topology

variable {G : Gauge} {n : Side} {V ι : Type} [DecidableEq V]
  {Γ : Census V} {Y : Rep G n} {w : V → ℝ} {o : V → Site n} {b : ℕ} {σ D : ℝ}

/-- A declared independent radius is scaled once for each actual occurrence
in a mark. Every charged row contains at least one external mark. -/
theorem fare (M : Menu.Hat Γ Y) (hw : ∀i,0<w i) {t : ℝ} (ht : 0<t) (h₁ : t≤1) :
    Menu.fare M (fun i => t*w i) ≤ t*Menu.fare M w := by
  have hc := Finset.card_pos.mpr M.shiny
  have hpow : t^M.s.val.card≤t := (pow_le_pow_of_le_one ht.le h₁ hc).trans_eq (pow_one _)
  have coeff : 0≤Poly.toll w M.s := (Poly.worth hw _).le
  simp only [Menu.fare,Menu.sumFee,Poly.toll,Finset.prod_mul_distrib,Finset.prod_const]
  calc
    _ ≤ (t*(∏ i∈M.s.val,w i)*‖M.charge‖)*M.M.weight :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow coeff) (norm_nonneg _)) M.M.profit
    _ = _ := by ring

/-- The original spatial offer on a full positive vector is transported to
smaller independent radii on the identical rows, locations and support. -/
theorem scale (M : ι → Menu.Hat Γ Y) (H : Menu.Offer o M w b σ D)
    (hw : ∀i,0<w i) {t : ℝ} (ht : 0<t) (h₁ : t≤1) :
    Menu.Offer o M (fun i=>t*w i) b σ (t*D) := by
  refine ⟨H.sites,fun z=>budget_mono (budget_scale ht.le (H.budget z)) ?_ ?_⟩
  · intro i
    split
    · exact mul_nonneg (Menu.Crew _ (fun i=>mul_pos ht (hw i))) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    dsimp only
    split_ifs
    · exact (mul_le_mul_of_nonneg_right (fare (M i) hw ht h₁)
        (Real.exp_nonneg _)).trans_eq (mul_assoc ..)
    · rw [mul_zero]

/-- The prebooked subpower price buys the original small shipping budget.
The rooted states, sign coefficients and source supports are unchanged. -/
theorem shipping (M : ι → Menu.Hat Γ Y) (H : Menu.Offer o M w b σ D)
    (hw : ∀i,0<w i) {β κ : ℝ} (hβ : 1≤β) (hκ : 0<κ) (cash : D≤β^κ) :
    Menu.Offer o M (fun i=>β^(-3*κ)*w i) b σ (β^(-2*κ)) := by
  have hp := zero_lt_one.trans_le hβ
  have ht : β^(-3*κ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hβ (by linarith)
  have hs := scale M H hw (Real.rpow_pos_of_pos hp _) ht
  have cost : β^(-3*κ)*D≤β^(-2*κ) := calc
    _ ≤ β^(-3*κ)*β^κ := mul_le_mul_of_nonneg_left cash (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [←Real.rpow_add hp]; congr 1; ring
  exact ⟨hs.sites,fun z=>budget_loosen (hs.budget z) cost⟩

/-- The all-orders boost on the actual measured fine coupling fits the
original radius after one threshold, uniformly in the upper cutoff and period. -/
theorem radius {C : Family G} (hC : C.Makes) (hG : G.Simple) {η : ℝ} (hη : 0<η) :
    ∀ᶠ i : ℕ in atTop,∀N p,i≤N →
      C.path.levels.clock.hatBeta i^((1-η)/2) * Pert.Asymptotics.regulatorRun C N p i≤1 := by
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [grow.eventually_ge_atTop (1:ℝ),
    ((tendsto_rpow_atTop (show 0<η/2 by linarith)).comp grow).eventually_ge_atTop 2] with i h hLarge
  intro N p hi
  let β := C.path.levels.clock.hatBeta i
  have hb : 0<β := zero_lt_one.trans_le h
  have hg := (IterationFour.Currency.hat_g hC N p i hi).2
  change Pert.Asymptotics.regulatorRun C N p i≤2*(Real.sqrt β)⁻¹ at hg
  have ht : 0≤β^((1-η)/2) := Real.rpow_nonneg hb.le _
  apply (mul_le_mul_of_nonneg_left hg ht).trans
  rw [←mul_assoc,←div_eq_mul_inv,div_le_one (Real.sqrt_pos.mpr hb),Real.sqrt_eq_rpow]
  calc
    β^((1-η)/2)*2 ≤ β^((1-η)/2)*β^(η/2) := mul_le_mul_of_nonneg_left hLarge ht
    _ = _ := by rw [←Real.rpow_add hb]; congr 1; ring

end YM.Integration.ManuscriptQLocalMarkerReserve
