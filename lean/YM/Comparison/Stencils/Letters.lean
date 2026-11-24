import YM.Comparison.Stencils.SeriesJet

/-!
# Bare log-symbol columns

The microscopic stencil is not identified by its name! Read the
construction's `SectionData`. Give a full expansion in the convention of
`S_h(g)` (engineering powers extra), the representation by genuine unmasked
plaquette stencils, and the algebraic normalization/check by `π_{i,h}`
at *all coupling orders*. Hypotheses supplied for the Family by consumer.

No markers/test derivatives yet; these are the address-zero entries. In
particular these bare columns do **not** include the cover Wick conversion
(or any self-pairing). We always keep all off-shell entries here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter Feed
open Planned.PrimaryIntegral295.Place (column Dev slant Spot pore column_smooth slant_smooth copy)
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {S : Finset Cover} {d : ℕ} {F : Labels.Frame G d} {H : Hol G}

/-- `f_α`. No length, coupling or threshold power absorbed here. -/
def cylinder (T : SectionData F) (i : F.Index) : CoverConfig G → ℂ :=
  T.evaluate (Pi.single i 1)

def columnSeries (T : SectionData F) (i : F.Index) : Feed.LogSeries G T.stencil := fun k =>
  symbol T.stencil (cylinder T i) (k+(F.grades i).2)

section Formula
open Bid

/-- Independent ordered formula using a presentation by slot stencils. -/
def formsSeries (A : Links ℤ G.Color) (ℓ : ℕ) {n : ℕ} (B : Fin n → Slot) (P : Pose G n) :=
  undress ℓ P fun u => slotSeries A (B u.1) u.2

theorem forms_exact (A : Links ℤ G.Color) {ℓ n : ℕ} (B : Fin n → Slot) {P : Pose G n}
    (h : Bid.lows P ℓ) :
    recording (fun t : ℝ => lumin P (mapped B (linksOf (t • A)))) =
      PowerSeries.X ^ ℓ * formsSeries A ℓ B P := by
  let u : Fin n × G.ColorIndex → ℝ → ℂ := fun i r => scalarSlot (B i.1) i.2 (linksOf (r • A))
  change recording (fun t => MvPolynomial.eval (fun i => u i t) P) = _
  rw [recording_pol P (u := u) (by intro i; exact (slot_smooth A _ _).contDiffAt)]
  simp_rw [u, recording_slot]
  exact undress_exact h _

/-- The degree zero formula keeps exactly slot number, with the indicated
linear lattice curls. Finite-support horizontal form, including the constant
field if present. -/
theorem forms_leading (A : Links ℤ G.Color) {ℓ n : ℕ} (B : Fin n → Slot) {P : Pose G n}
    (h : Bid.lows P ℓ) :
    PowerSeries.coeff 0 (formsSeries A ℓ B P) =
      lumin (portion ℓ P) (fun j => Exterior.linkSum A (B j).offset
                  (square (B j).plaq.val.1 (B j).plaq.val.2)) := by
  let Z (Q : Pose G n) := MvPolynomial.eval₂Hom PowerSeries.C
    (fun j : Fin n × G.ColorIndex => slotSeries A (B j.1) j.2) Q
  let y (j : Fin n) := Exterior.linkSum A (B j).offset (square (B j).plaq.val.1 (B j).plaq.val.2)
  have he Q : PowerSeries.coeff 0 (Z Q) = lumin Q y := by
    unfold Z lumin
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    induction Q using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]; simp
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X,
        ← PowerSeries.coeff_zero_eq_constantCoeff, slot_linear]
  change PowerSeries.coeff 0 (∑ a ∈ P.support, PowerSeries.X ^ (slots a - ℓ) * Z (MvPolynomial.monomial a (P.coeff a))) = _
  classical
  unfold lumin portion
  rw [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, map_sum]
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hl : slots a = ℓ
  · rw [hl, Nat.sub_self, pow_zero, one_mul, he]
    rw [if_pos]; rfl
    unfold slots at hl; simpa [Finsupp.weight_apply] using hl
  have hm := h a ha
  change ℓ ≤ slots a at hm
  rw [if_neg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  unfold slots at hl; simpa [Finsupp.weight_apply] using hl

/-- Construction stencil binding can be kept or changed within its
exact presentation hypotheses; no dependence on parsing for the series. -/
structure ColumnsUse (T : SectionData F) (i : F.Index) where
  width : ℕ
  uses : Fin width → Slot
  room j : (uses j).stencil ⊆ T.stencil
  form : Pose G width
  min_degree : lows form (F.grades i).2
  reveals : cylinder T i = lumin form ∘ mapped uses

lemma supplied (T : SectionData F) (h : pop T) (i) : Nonempty (ColumnsUse T i) := by
  obtain ⟨n,A,hB,P,hP,hq⟩ := h i
  exact ⟨⟨n,A,hB,P,hq,hP⟩⟩

lemma origin_series (T : SectionData F) (i : F.Index) (V : ColumnsUse T i) (A : Links ℤ G.Color) :
    recording (fun t : ℝ => cylinder T i (linksOf (t • A))) =
      PowerSeries.X ^ (F.grades i).2 * formsSeries A (F.grades i).2 V.uses V.form := by
  rw [V.reveals]; exact forms_exact _ _ V.min_degree

lemma column_value (T : SectionData F) (i : F.Index) (t : ℕ) (A : Links ℤ G.Color) :
    inscribe (Symbols.patch T.stencil A) (columnSeries T i t) =
      CubicMatch.term (t+(F.grades i).2) (fun r : ℝ => cylinder T i (linksOf (r • A))) :=
  symbol_value _ (T.cylinder_local _) _ _ ((column_smooth T i).contDiffAt.of_le le_top)

/-- Independent path evaluation of *every coefficient* of the delivered
polynomial symbols. Equivalent on real link slots, hence identifies the
polynomial data, irrespective of stencil-presentation choices. -/
theorem column_reads (T : SectionData F) (i : F.Index) (V : ColumnsUse T i) (A : Links ℤ G.Color) (k : ℕ) :
    inscribe (Symbols.patch T.stencil A) (columnSeries T i k) =
      PowerSeries.coeff k (formsSeries A (F.grades i).2 V.uses V.form) := by
  rw [column_value, ← recorded, origin_series T i V A, PowerSeries.coeff_X_pow_mul]

/-- For these stencils there are no missing (negative-coupling-power)
terms. This is a consequence of the *valuation*, not true for an arbitrary
stencil merely projecting to this weight. -/
lemma vanishing (T : SectionData F) (i : F.Index) (V : ColumnsUse T i) (k : ℕ) (hk : k < (F.grades i).2) :
    symbol T.stencil (cylinder T i) k = 0 := by
  apply inscribe_ext
  intro x
  rw [map_zero, ← drops x, symbol_value (cylinder T i) (T.cylinder_local (Pi.single i 1)) (widen x) k
    ((column_smooth T i).contDiffAt.of_le le_top), ← recorded, origin_series T i V (widen x),
    PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hk)]
end Formula

section Classical
-- First project the *undivided* stencil (arbitrary projection hypotheses, no
-- linear independence), through engineering order d.
lemma gross (H : Hol G) (d : ℕ) (f : CoverConfig G → ℂ) (hr : LocalOn S f)
    (hf : ContDiffAt ℝ d (fun x : Dev S G => f (pore x)) 0) (k : ℕ) (hk : k ≤ d) (J : Jet G) :
    iteratedDeriv k (fun h => f (H.links d J h)) 0 =
      iteratedDeriv k (fun h => reading H d (∑ j ∈ Finset.range (d+1), symbol S f j) (trail J d h)) 0 := by
  let X (t : ℝ) := rule S H d (trail J d t)
  let F : Dev S G → ℂ := f ∘ pore
  have he : (fun h => f (H.links d J h)) =ᶠ[𝓝 0] F ∘ X := by
    have hu : Tendsto (trail J d) (𝓝 0) (𝓝 0) := (trail_root J d) ▸ (trail_smooth J d).continuous.tendsto 0
    filter_upwards [hu.eventually (germ S H d)] with t ht
    rw [scales H (d := d) J]
    exact (hr _ _ ht).symm
  have hX : X 0 = 0 := by simp only [X, trail_root, rule_zero]
  have ht : ContDiffAt ℝ ω X 0 := ContDiffAt.comp (f := trail J d) (g := rule S H d) 0
    ((trail_root J d).symm ▸ rule_diff S H d) (trail_smooth J d).contDiffAt
  have hv : iteratedFDeriv ℝ k (F ∘ X) 0 =
      iteratedFDeriv ℝ k (Work.G05.blockTaylor d F ∘ X) 0 :=
    Work.G05.jets_comp (ht.of_le (m := d) le_top) (ht.of_le le_top) (hX.symm ▸ hf)
      (Work.G05.blockTaylor_contDiff d F _).contDiffAt rfl (fun _ _ => rfl)
      (fun i hi => by rw [hX]; exact (Work.G05.blockTaylor_jets (f := F) hf i hi).symm) k hk
  have hy : (fun h => reading H d (∑ j ∈ Finset.range (d+1), symbol S f j) (trail J d h)) =
      Work.G05.blockTaylor d F ∘ X := by
    funext t
    simp only [reading, Work.G05.blockTaylor, map_sum, symbol_patch, comp_apply, Finset.sum_apply]
    rfl
  rw [he.iteratedDeriv_eq, hy]; exact DFunLike.congr_fun hv _

theorem warranty {f : CoverConfig G → ℂ} (hr : LocalOn S f)
    (hf : ContDiffAt ℝ d (fun x : Dev S G => f (pore x)) 0) {p : Label G d} (h : Projects H p f) :
    projector H d (∑ j ∈ Finset.range (d+1), symbol S f j) = p.val := by
  apply sole_poly _ _ d (raw_cap ..) p.property.1
  intro J k hk
  change iteratedDeriv k (fun u => Labels.read (scaleJet J u) (rawPi (S := S) _ d _)) 0 = _
  rw [geometry _ _ _ J k hk, ← gross H d f hr hf k hk J]
  exact (h J).2.2 k hk

lemma begins (T : SectionData F) (h : T.Sound H) (i : F.Index) :
    projector H d (∑ j ∈ Finset.range (d+1), symbol T.stencil (cylinder T i) j) = (F.basis i).val :=
  warranty (T.cylinder_local (Pi.single i 1)) ((column_smooth T i).contDiffAt.of_le le_top)
    ((show F.coords.symm (Pi.single i 1) = F.basis i from
        (F.coords_basis i) ▸ F.coords.symm_apply_apply _ ) ▸ h.projects (Pi.single i 1))

lemma inherits (T : SectionData F) (i : F.Index) (V : ColumnsUse T i) (e : ℕ) (h : T.Sound H) :
    stage H d e (columnSeries T i) = portion (e+(F.grades i).2) (F.basis i).val := by
  let ℓ := (F.grades i).2
  let f (q : ℕ) := portion (e+ℓ) (projector H d (symbol T.stencil (cylinder T i) q))
  have h₁ : ∑ i ∈ Finset.range ℓ, f i = 0 := Finset.sum_eq_zero fun j hj => by
    dsimp only [f]
    rw [vanishing T i V _ (Finset.mem_range.mp hj), map_zero, map_zero]
  calc
    stage H d e (columnSeries T i) = ∑ j ∈ Finset.range (ℓ+(e+1)), f j := by
      rw [Finset.sum_range_add, h₁, zero_add, stage_at]
      apply Finset.sum_congr rfl
      intro b hb
      have ht := Finset.mem_range.mp hb
      rw [booth_one H d _ (p := columnSeries T i b) (k := b+ℓ)
        (symbol_rank T.stencil (cylinder T i) _), show b+ℓ+(e-b)=e+ℓ by omega]
      change portion _ (projector H d (symbol _ _ (b+ℓ))) = f (ℓ+b)
      rw [add_comm b ℓ]
    _ = ∑ j ∈ Finset.range (d+1), f j := by
      by_cases he : d+1 ≤ ℓ+(e+1)
      · refine Eq.symm (Finset.sum_subset (Finset.range_mono he) ?_)
        intro j _ hj; simp only [Finset.mem_range, Nat.not_lt] at hj
        exact (congrArg _ (projection_zero H d (symbol_rank T.stencil (cylinder T i) j) (by omega))).trans
          (map_zero (portion (R := ℂ) (σ := Key G) (e+ℓ)))
      refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
      intro j _ hj; simp only [Finset.mem_range,Nat.not_lt] at hj
      exact projection_rank H d (symbol_rank T.stencil (cylinder T i) j) (by omega)
    _ = _ := by rw [← begins T h i, map_sum, map_sum]

lemma column_normal (T : SectionData F) (i : F.Index) (V : ColumnsUse T i) (e : ℕ) (h : T.Sound H) :
    stage H d e (columnSeries T i) = if e=0 then (F.basis i).val else 0 := by
  let ℓ := (F.grades i).2
  have hv : Rank (F.basis i).val ℓ := by
    rw [rank_slot]
    exact fun a ha => congrArg Prod.snd <| (Labels.weight_slot a).symm.trans
      ((pure_grade _ _).1 (F.pure i) (MvPolynomial.mem_support_iff.mp ha))
  rw [inherits T i V e h, on_rank _ _ hv]
  simp [ℓ]
end Classical

/-- Entire primary top column packet. Complex column normalizations are
applied on the *same* underlying real section. -/
def columns (T : SectionData F) : F.Coeff →ₗ[ℂ] LogSeries G T.stencil where
  toFun p := ∑ i : F.Index, p i • columnSeries T i
  map_add' p q := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' x p := by simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul, RingHom.id_apply]

lemma columns_basis (T : SectionData F) (i : F.Index) : columns T (Pi.single i 1) = columnSeries T i := by
  classical
  change ∑ j : F.Index, (Pi.single i (1:ℂ) : F.Coeff) j • columnSeries T j = _
  simp

/-- The normalization in the exact `π` and `S_h` conventions, polynomial
coordinates. In particular positions/h-erased, equation sector retained. -/
theorem normalization (T : SectionData F) (H : Hol G) (hT : T.Sound H) (h : Bid.pop T) (x : F.Coeff)
    (e : ℕ) :
    stage H d e (columns T x) = if e=0 then (F.coords.symm x).val else 0 := by
  classical
  change stage _ _ _ (∑ i : F.Index, x i • columnSeries T i) = _
  simp_rw [map_sum, map_smul, column_normal T _ (Classical.choice (supplied T h _)) _ hT]
  split_ifs with he
  · have hr : (F.coords.symm x).val = ∑ i : F.Index, x i • (F.basis i).val := by
      conv_lhs => rw [← F.basis.sum_repr (F.coords.symm x)]
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun z : ℂ => z • _) (congr_fun (F.coords.apply_symm_apply x) i)
    exact hr.symm
  simp
end YM.Comparison.Stencils
