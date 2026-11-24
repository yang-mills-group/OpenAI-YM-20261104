import YM.Integration.ActualStartupMaskedAction
import YM.Integration.ActualRunStartupInput
import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.WilsonLimitConstruction.FundedWilsonGerm
import YM.IntegrationR2.Rose.Top
import YM.CommonPhysical.Plaquette
import YM.Pert.Kinetic.Densities

/-! The original run's startup album on the genuine Wilson ray at variable
positive inverse coupling, including the entire native unspent plaquette. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonStartup

open Function Filter Finset Lattice Wilson RG Work Exterior PhysicalNext.Repeat.Legato
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open YM.IterationFour YM.IterationFour.Vacuum Progress.DirectedRecipe
open LocalComparison.Global
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side}

private theorem clear_owed (c : Clip) (P : BudgetPoint) (i : Key n) (U : Config G n)
    (hU : flags P.threshold U = ∅) : Key.owed c P i U = 0 := by
  have hf : flags P.threshold (i.frame U) = ∅ := by
    exact Finset.image_eq_empty.mp ((H03.flags_send i.1 i.native P.threshold U).trans hU)
  have hh (p : Cell n) : Healthy P.threshold (touched p) (i.frame U) := by
    simp [Healthy,hf]
  have hk : PathData.kept c P.threshold i.root.1 (i.frame U) := by
    intro p
    apply (healthy_chord p _ (hh p)).trans
    exact le_mul_of_one_le_right P.threshold_pos.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) c.radius_pos.le))
  simp only [Key.owed,due,if_neg (not_lt.mpr (healthy_chord i.root _ (hh i.root))),
    if_pos (hh i.root),if_pos hk,sub_self]

theorem unmask (P : BudgetPoint) (g : ℝ) (U : Config G n) (hU : flags P.threshold U = ∅)
    (L : List (Piece G n)) :
    Render.renders (Render.prefactor g) P U L = unmaskedLayers L g U := by
  have h (Q : Payload G n) : Q.amount P U = unmaskedPayload Q U := by
    unfold Payload.amount unmaskedPayload
    exact tsum_congr fun i => masked_eq _ _ _ _ (by simp [Healthy,hU])
  induction L with
  | nil => rfl
  | cons a L ih => simp only [Render.renders,h,ih,unmaskedLayers,List.map_cons,List.sum_cons]

/-- The authentic original unspent curvature polynomial, summed over all
original orientations with their original scalar. -/
def residual (S : Stage) (r : ℕ) (U : Config G n) : ℝ :=
  WilsonStartup.share * WilsonStartup.Design.bulk S.clip *
    ∑ i : Key n, WilsonStartup.leftOver (r+2) i.positive U

private theorem chip_price (r : ℕ) (u : G.El) :
    chip G r (G.mat u) = Quad.Rose.stub (r+2) u := by
  unfold chip
  rw [Quad.surplus_actual,Quad.k_actual,← Quad.Rose.reveal4]
  unfold Quad.Rose.stub Quad.Rose.pre
  simp only [Pi.sub_apply]
  ring

theorem stored (P : BudgetPoint) (S : Stage) (hc : S.clip.direct ≤ 1)
    (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (U : Config G n)
    (hU : flags P.threshold U = ∅) :
    (Design.top G S.clip).inChannels S.clip P β U +
      unmaskedLayers (album G n P S r) (Currency.gain β) U +
      β * residual S r U = β * energy U := by
  have hs := ActualStartupMaskedAction.raw_split (G := G) P S r hr β hβ U
  rw [unmask P _ U hU] at hs
  have ht : (slate G n (Start.weight S.clip β) (chip G r)).amount P U =
      β * residual S r U := by
    rw [tally]
    have hp (i : Key n) : masked P.threshold i.skin (element G (chip G r) i.positive) U =
        WilsonStartup.leftOver (r+2) i.positive U := by
      rw [masked_eq _ _ _ _ (by simp [Healthy,hU])]
      exact chip_price r _
    simp_rw [hp]
    unfold residual Start.weight
    ring
  rw [ht] at hs
  have h := channel_split S.clip P U hc β
  simp only [clear_owed S.clip P _ U hU,Finset.sum_const_zero,mul_zero,add_zero] at h
  rw [add_assoc,← hs,Start.written_sum]
  exact h

/-- A single field germ supplies every inverse coupling and its own native
finite album, original kinetic path and unspent field on the funded run. -/
theorem germ (R : Run G) (T : Campaign R) (N p r : ℕ) (hr : 2 ≤ r)
    (B : fieldDir G (R.family.side N p) 1) :
    let X := R.family.path.rep N p N
    let S := R.family.path.levels.params N
    ∀ᶠ t : ℝ in 𝓝 0, ∀ β : ℝ, 0 < β →
      X.path.inChannels X.clip X.p β (FundedWilsonGerm.ray B t) +
        unmaskedLayers (album G _ X.p S r) (Currency.gain β) (FundedWilsonGerm.ray B t) +
        β * residual S r (FundedWilsonGerm.ray B t) = β * FundedWilsonGerm.action B t := by
  dsimp only
  let X := R.family.path.rep N p N
  have hf := Pert.Kinetic.rays_free X.p.threshold X.p.threshold_pos (collect G B)
  have hp := ActualRunStartupInput.represented_path R T N p
  have hc : (R.family.path.rep N p N).clip = (R.family.path.levels.params N).clip :=
    (R.makes.wilson.represents N p N le_rfl).clip
  have hd := Push.PriceCompiler.Canonical.direct_le_one (R.alloy.B.support.cap N N le_rfl).metric
  filter_upwards [hf] with t ht
  intro β hβ
  rw [hp,hc]
  have hs : collect G (t • B) = t • collect G B := by funext e; rfl
  apply stored X.p _ hd r hr β hβ
  change flags X.p.threshold (increment 1 (collect G (t • B))) = ∅
  rw [hs]
  exact ht

/-- At the inverse-square coupling this is exactly the finite fine-side
kinetic and unmasked layer germ entering the physical comparison. -/
theorem pointed (R : Run G) (T : Campaign R) (N p r : ℕ) (hr : 2 ≤ r)
    (B : fieldDir G (R.family.side N p) 1) (C : FundedWilsonGerm.Curve B) :
    let X := R.family.path.rep N p N
    let S := R.family.path.levels.params N
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      X.path.inChannels X.clip X.p ((t^2)⁻¹) (FundedWilsonGerm.ray B t) +
        unmaskedLayers (album G _ X.p S r) t (FundedWilsonGerm.ray B t) +
        (t^2)⁻¹ * residual S r (FundedWilsonGerm.ray B t) = C.value t := by
  dsimp only
  filter_upwards [(germ R T N p r hr B).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t h ht
  have hs : 0 < t := ht
  have hgain : Currency.gain ((t^2)⁻¹) = t := by
    simp [Currency.gain,Real.sqrt_inv,Real.sqrt_sq hs.le]
  have hprice := h ((t^2)⁻¹) (by positivity)
  rw [hgain,C.factor t,inv_mul_cancel_left₀ (pow_ne_zero _ hs.ne')] at hprice
  exact hprice

end YM.Integration.WilsonLimitConstruction.FundedWilsonStartup
end
