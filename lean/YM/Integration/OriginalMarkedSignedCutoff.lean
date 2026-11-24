import YM.Gaps1020.Local.Wear
import YM.Integration.ActualPolynomialContraction

/-! Signed comparison with the retained marked density at a physical cutoff.
The two densities share all forced entries, including their vacuum partners.
The remaining ordinary rows have the original rooted radial price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedSignedCutoff
open Function Filter Lattice RG Pressure Tree Wilson Finset MeasureTheory Marker Overlay
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Pressure.Stores Pressure.Tube
open PhysicalNext PhysicalNext.Repeat Height Greenbelt ConnectedActivityE6.Blaze
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open Push.SectorMeasure YM.GapsLocal.Full
open Next.Fluctuations Oriented Work.E03 Shell SliceRows Control Window Coat Footprint Raw Matter
open Blaze.March Captain Silica Stained Shield
open Gas Ursell Trees RG.Supply Org Roost Opera Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open PhysicalNext.Repeat.Daisy.Charity.RG12 YM.RG01.Survive
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Merge Photo MergeProof Accent
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {E : Census V} {G : Gauge}
    {n : Side} {P : Rep G n} {w : V → ℝ}

private theorem quiet (b : Bands E P) (h : b.Active) {u a d k : ℝ}
    (r : b.Radial w u a d k) (U : Config G n) : (b.extra U).part E.quiet = 0 := by
  have vanishes (i : E.Mode) (hi : i.val.Nonempty) (v : ℂ) :
      (Poly.send i v).part E.quiet = 0 := by
    rw [Poly.part_send, if_neg (show E.quiet ≠ i from fun he =>
      Finset.nonempty_iff_ne_empty.mp hi (congrArg Subtype.val he.symm))]
  rw [Bands.extra, Poly.part_plus, Poly.share (b.bulkBound h r U).1, Poly.part_sum]
  simp_rw [Bands.ray, vanishes _ (h.proper _),
    vanishes _ (show (E.fire _).val.Nonempty from Finset.singleton_nonempty _),
    tsum_zero, sum_const_zero, zero_add]

private theorem pass_price (z : Poly E) (hw : ∀ i, 0 < w i) (hz : z.part E.quiet = 0) :
    Poly.price w (Poly.pass z - 1) ≤ Real.exp (Poly.price w z) - 1 := by
  let x := Poly.pass z
  have hx : x.part E.quiet = 1 := Poly.pass_part z hz
  have h : Poly.price w (x-1) + 1 = Poly.price w x := by
    let f i := Poly.toll w i * ‖(x-1).part i‖
    let g i := Poly.toll w i * ‖x.part i‖
    change (∑ i, f i) + 1 = ∑ i, g i
    rw [← Finset.sum_erase_add _ f (Finset.mem_univ E.quiet),
      ← Finset.sum_erase_add _ g (Finset.mem_univ E.quiet)]
    have part i : (x-1).part i = x.part i - (1 : Poly E).part i := rfl
    have hf : f E.quiet = 0 := by unfold f; rw [part, Poly.one_part, hx]; simp
    have hg : g E.quiet = 1 := by unfold g; rw [hx]; simp
    rw [hf, hg, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    unfold f g
    rw [part, Poly.one_part, if_neg (Finset.ne_of_mem_erase hi), sub_zero]
  exact (eq_sub_of_add_eq h).le.trans (sub_le_sub_right (Poly.pass_budget hw _) 1)

/-- All proper marked subtuples of one requested coefficient. -/
def lower (q : E.Mode) (x : Poly E) : Poly E :=
  Poly.inject (fun j => if j.val ⊂ q.val then x.part j else 0)

omit [Fintype V] in
private theorem proper_product (d y : Poly E) (hd : d.part E.quiet = 0) (q : E.Mode) :
    (d * y).part q = (d * lower q y).part q := by
  rw [Poly.part_mul, Poly.part_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hm : Poly.merges i j q
  · simp only [if_pos hm]
    by_cases hi : i = E.quiet
    · simp only [hi, hd, zero_mul]
    have hs : j.val ⊂ q.val := by
      rw [← hm.2]
      refine Finset.ssubset_iff_of_subset Finset.subset_union_right |>.2 ?_
      have hn : i.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he => hi (Subtype.ext he)
      obtain ⟨z, hz⟩ := hn
      exact ⟨z, Finset.mem_union_left _ hz, fun hj => Finset.disjoint_left.mp hm.1 hz hj⟩
    change _ = _ * (if j.val ⊂ q.val then _ else _)
    rw [if_pos hs]
  simp only [if_neg hm]

private theorem split (a b e : Bands E P)
    (units : a.units = b.units) (zero : e.units = 0)
    (sb : a.support = b.support) (se : a.support = e.support)
    (rb : a.rays = b.rays) (re : a.rays = e.rays) (rows : a.H = b.H + e.H)
    {u c d k v c' d' k' : ℝ} (hb : b.Active) (he : e.Active)
    (br : b.Radial w u c d k) (er : e.Radial w v c' d' k') (U : Config G n) :
    a.extra U = b.extra U + e.extra U := by
  have ray i : a.ray i U = b.ray i U + e.ray i U := by
    by_cases healthy : Healthy P.p.threshold (a.support i) U
    · have hb := sb ▸ healthy
      have he := se ▸ healthy
      simp only [Bands.ray, masked_eq _ _ _ _ healthy, masked_eq _ _ _ _ hb,
        masked_eq _ _ _ _ he, rows, Pi.add_apply, ←rb, ←re]
      ext j
      rw [Poly.part_plus]
      simp only [Poly.part_send]
      split <;> simp
    · have hb := sb ▸ healthy
      have he := se ▸ healthy
      simp only [Bands.ray, masked_ne _ _ _ _ healthy, masked_ne _ _ _ _ hb,
        masked_ne _ _ _ _ he, Poly.send_zero, zero_add]
  unfold Bands.extra
  simp only [units, zero, Pi.zero_apply, Poly.send_zero, sum_const_zero, zero_add]
  rw [show (fun i => a.ray i U) = fun i => b.ray i U + e.ray i U from funext ray,
    (b.bulkBound hb br U).1.tsum_add (e.bulkBound he er U).1, add_assoc]

section physical
variable {ι : Type} [Fintype ι] [Nonempty V] {c f L : Side} {W s μ C : ℝ}
    {S : StepData c f} {T : Tube G S} {Pt : Teller G} {Q : ConnectedActivityE6.Target G Pt}
    {o : Target.Order G W} {R : Rep G f} {H : Cash W s μ L Q o C T R}
    {A : Rep G c} {fields : ι → Lotus.Leaf R} {cost : ι → ℝ} {g : ι → Poly E}
    {hard : ℝ → Finset ι → Ovens.Code G c} {p : V → Site c} {i : V → ℂ} {M : ℕ}
    {u a b k : ℝ}

local notation "Z(" x "," l ")" => scenery fields (H:=H) cost g l x p A hard Chi.canonical M
local notation "funded" => Z(i, fun q => ¬ M+1 ≤ q)
local notation "error" => Z(0, fun q => M+1 ≤ q)
local notation "whole" => Z(i, fun _ => True)
local notation "push" => S.push R.beta (litGiven (S:=S) fields cost g i)

/-- The signed polynomial retains every disconnected product in the funded
density and every hard partner in its common gas. -/
theorem factorization (h : Claim H A fields cost g hard p i M w u a b k) (U : Config G c) :
    push U - (funded).density U = (Poly.pass ((error).extra U) - 1) * (funded).density U := by
  rw [h.push]
  have hs := split whole funded error rfl rfl rfl rfl rfl rfl h.union
    h.funded.1 h.remainder.1 h.funded.2 h.remainder.2 U
  have hf := quiet funded h.funded.1 h.funded.2 U
  have he := quiet error h.remainder.1 h.remainder.2 U
  have hgas : (whole).cluster U = (funded).cluster U := rfl
  simp only [Bands.density, hs, Extra.Trajectories.pass_add hf he, hgas,
    Algebra.smul_def, sub_mul, one_mul]
  ring

/-- The exact error has an alternative expression in terms of the complete
pushed density, whose modes are the physical input correlations. -/
theorem source_factorization (h : Claim H A fields cost g hard p i M w u a b k)
    (U : Config G c) :
    push U - (funded).density U = (1 - Poly.pass (-((error).extra U))) * push U := by
  have he := quiet error h.remainder.1 h.remainder.2 U
  have hn : (-((error).extra U)).part E.quiet = 0 := by rw [Poly.part_neg, he, neg_zero]
  have hunit : Poly.pass (-((error).extra U)) * Poly.pass ((error).extra U) = 1 := by
    rw [← Extra.Trajectories.pass_add hn he, neg_add_cancel, Extra.Trajectories.pass_zero]
  have hfull : push U = Poly.pass ((error).extra U) * (funded).density U := by
    have eq := factorization h U
    rw [sub_mul, one_mul] at eq
    simpa only [sub_add_cancel] using congrArg (· + (funded).density U) eq
  rw [hfull, sub_mul, one_mul, ← mul_assoc, hunit, one_mul]

/-- Only lower physical moments enter the signed error of an arbitrary
marked coefficient, including all mixed terms. -/
theorem proper_price (h : Claim H A fields cost g hard p i M w u a b k)
    (q : E.Mode) (U : Config G c) :
    Poly.toll w q * ‖(push U - (funded).density U).part q‖ ≤
      (Real.exp (Fintype.card V * a) - 1) * Poly.price w (lower q (push U)) := by
  let d := 1 - Poly.pass (-((error).extra U))
  have he := quiet error h.remainder.1 h.remainder.2 U
  have hn : (-((error).extra U)).part E.quiet = 0 := by rw [Poly.part_neg, he, neg_zero]
  have hd : d.part E.quiet = 0 := by
    change (1 : Poly E).part E.quiet - (Poly.pass _).part E.quiet = 0
    rw [Poly.one_part, if_pos rfl, Poly.pass_part _ hn, sub_self]
  have hcost : Poly.price w d ≤ Real.exp (Fintype.card V * a) - 1 := by
    have hneg (x : Poly E) : Poly.price w (-x) = Poly.price w x := by
      simp only [Poly.price, Poly.part_neg, norm_neg]
    rw [show d = -(Poly.pass (-((error).extra U)) - 1) by
      unfold d; rw [neg_sub], hneg]
    apply (pass_price _ h.remainder.2.pure hn).trans
    apply sub_le_sub_right (Real.exp_monotone _) 1
    rw [hneg]
    simpa only [zero_add] using ((error).bulkBound h.remainder.1 h.remainder.2 U).2
  rw [source_factorization h U, proper_product d (push U) hd q]
  exact ((Poly.member h.remainder.2.pure _ _).trans
    (Poly.multiplication h.remainder.2.pure _ _)).trans
    (mul_le_mul_of_nonneg_right hcost (Poly.nonnegative h.remainder.2.pure _))

/-- Pointwise signed discrepancy at the actual input coupling, for every
polynomial mode simultaneously. -/
theorem signed_price (h : Claim H A fields cost g hard p i M w u a b k) (U : Config G c) :
    Poly.price w (push U - (funded).density U) ≤
      (Real.exp (Fintype.card V * a) - 1) * Poly.price w ((funded).density U) := by
  rw [factorization h U]
  have ht := (pass_price ((error).extra U) h.remainder.2.pure
    (quiet error h.remainder.1 h.remainder.2 U)).trans
    (sub_le_sub_right (Real.exp_monotone (by
      simpa only [zero_add] using ((error).bulkBound h.remainder.1 h.remainder.2 U).2)) 1)
  exact (Poly.multiplication h.remainder.2.pure _ _).trans
    (mul_le_mul_of_nonneg_right ht (Poly.nonnegative h.remainder.2.pure _))

/-- The prescribed counterterm remains an independently supplied polynomial.
Its mismatch with the funded density is measured on the same configuration. -/
theorem prescribed (h : Claim H A fields cost g hard p i M w u a b k)
    (model : Config G c → Poly E) (U : Config G c) :
    Poly.price w (push U - model U) ≤
      (Real.exp (Fintype.card V * a) - 1) * Poly.price w ((funded).density U) +
      Poly.price w ((funded).density U - model U) := by
  rw [show push U - model U = (push U - (funded).density U) + ((funded).density U - model U) by abel]
  exact (Poly.addition h.remainder.2.pure _ _).trans
    (add_le_add (signed_price h U) le_rfl)

/-- The mode with one marked point uses the physical vacuum alone.
In particular the extensive absolute gas price cancels. -/
theorem single (h : Claim H A fields cost g hard p i M w u a b k)
    {δ κ : ℝ} (law : A.activities.Valid A.p δ κ) (v : V) (U : Config G c) :
    (push U - (funded).density U).part (E.fire v) =
      ((error).extra U).part (E.fire v) * (A.eval U : ℂ) := by
  rw [factorization h U, Accent.shock]
  have he := quiet error h.remainder.1 h.remainder.2 U
  have hz : (Poly.pass ((error).extra U) - 1).part E.quiet = 0 := by
    change (Poly.pass ((error).extra U)).part E.quiet - (1 : Poly E).part E.quiet = 0
    rw [Poly.pass_part _ he, Poly.one_part]
    simp
  have hs : (Poly.pass ((error).extra U) - 1).part (E.fire v) = ((error).extra U).part (E.fire v) := by
    change (Poly.pass ((error).extra U)).part (E.fire v) - (1 : Poly E).part (E.fire v) = _
    rw [Accent.whisper _ _ he, Poly.one_part, if_neg (E.fire_hot v), sub_zero]
  rw [hz,hs,zero_mul,zero_add,(funded).same h.funded.1 h.funded.2 law]

/-- A bound relative to the actual pointwise Wilson density. Its constant
depends only on the number of external marks and the paid tail order. -/
theorem single_relative (h : Claim H A fields cost g hard p i M w u a b k)
    {δ κ : ℝ} (law : A.activities.Valid A.p δ κ) (v : V) (U : Config G c)
    (hp : 0 ≤ A.eval U) :
    w v * ‖(push U - (funded).density U).part (E.fire v)‖ ≤
      (Fintype.card V * a) * A.eval U := by
  rw [single h law v U, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hp
  have hf := (Poly.member h.remainder.2.pure (E.fire v) ((error).extra U)).trans
    ((error).bulkBound h.remainder.1 h.remainder.2 U).2
  simpa only [Poly.solo_toll, zero_add] using hf

/-- The Haar numerator uses its own partition; bounded exterior tests
are allowed on the same configuration. -/
theorem single_integral (h : Claim H A fields cost g hard p i M w u a b k)
    {δ κ : ℝ} (law : A.activities.Valid A.p δ κ) (v : V)
    (test : Config G c → ℂ) (ht : ∀ U, ‖test U‖ ≤ 1)
    (hp : ∀ U, 0 ≤ A.eval U) (hv : Integrable A.eval (prior G c))
    (Z : ℝ) (hZ : 0 < Z) (norm : ∫ U, A.eval U ∂prior G c = Z) :
    w v * ‖∫ U, test U * (push U - (funded).density U).part (E.fire v) ∂prior G c‖ / Z ≤
      Fintype.card V * a := by
  let e (U : Config G c) := test U * (push U - (funded).density U).part (E.fire v)
  have hw := (h.remainder.2.pure v).le
  have hb (U) : w v * ‖e U‖ ≤ (Fintype.card V * a) * A.eval U := by
    unfold e
    rw [norm_mul]
    apply le_trans _ (single_relative h law v U (hp U))
    gcongr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ht U)
      (norm_nonneg ((push U - (funded).density U).part (E.fire v)))
  rw [div_le_iff₀ hZ, ← norm, ← integral_const_mul]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw)
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun U => mul_nonneg hw (norm_nonneg (e U)))
    (hv.const_mul _) (ae_of_all _ hb)

end physical
end YM.Integration.OriginalMarkedSignedCutoff
end
