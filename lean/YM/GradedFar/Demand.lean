import YM.FVA2.O.Canon.Docket
/-!
# (F.O), (F.1): what prices we have *before* inserting fields

In this file and the following ones we use the actual data structures/power conventions of the
FVA2 proof. In particular `A : Scale.Arenas G`, `O.Score.install A` (zero off `conf`).
`O.Canon.Physical` is on these **formal series**. In the application it and the scale law
are already given by the Match on our independent prescription. The price inputs in
`WiderProfiles.separate_predictor_inputs` are re-derived the same way below. None of the
bounds used here are inferred e.g. from comparing against finite-mesh entries at these positions.

Write `s : ℝ`, `T = exp s`, `x ∈ K ⊆ conf n`, `y ∈ S ⊆ Outside m`
(far shape has all points distinct from each other and from origin). Then
`squeeze (-s) y = T • y`. `ChargeP d a` is through power-series degrees **strictly less than d**,
with a power-log cost `post a s k = (1+s)^k exp(-a s)` eventually as `s → ∞`; it already encodes
uniformity over a parameter domain. Profiles are in `x,y`, both compact; clearance lemma
`layout_eventually` below on these same sets.

We also prove the graded far-field consequence (full uninserted `G^X` read retains `T^(-W)`
decay). For the joint/cancellation calculations later it's important that these `party`,
`lonelyG`, `Lamp` and `Basket` are on the same layouts, basis **and powers** as the series we
operate with, see `Operands` et seq.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open MS XSpace XSpace.Normalize XSpace.Structure1 Dframe
open O Seam O.Score Enh Scale
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m : ℕ}
variable {K : Set (Points n)} {S : Set (Points m)} {A : Arenas G}
    {ψ : ℝ → PowerSeries ℂ} {F : ℝ → Frames G} (H : Canon.Physical A ψ F)
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)

section spatial
include hK hx hS hy
/-- For all sufficiently large T the actual full & replacement layouts are in `conf`. -/
theorem layout_eventually : ∀ᶠ s : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ S,
    forest x (squeeze (-s) y) ∈ conf (n+m) ∧ outgoing (squeeze (-s) y) ∈ conf (1+m) := by
  have hsep (i : Fin n) (j : Fin m) : ∀ᶠ s : ℝ in atTop,
      ∀ x ∈ K, ∀ y ∈ S, ‖Theater.out (x i)‖ < ‖Theater.out (squeeze (-s) y j)‖ := by
    obtain ⟨C,_,hC⟩ := Legs K hK i
    obtain ⟨b,hb,hB⟩ := storyY hS hy j
    have hp := (Real.tendsto_exp_atTop.atTop_mul_const hb).eventually (eventually_gt_atTop C)
    filter_upwards [hp] with s hs x hX y hY
    rw [norm_g, norm_smul_of_nonneg (Real.exp_pos _).le]
    exact (lt_of_le_of_lt (hC x hX) hs).trans_le (mul_le_mul_of_nonneg_left (hB y hY) (Real.exp_pos _).le)
  filter_upwards [eventually_all.mpr (fun i : Fin n => eventually_all.mpr (hsep i))]
    with s hs x hX y hY
  have hZ := lives (-s) (hy hY)
  exact ⟨forest_sep (hx hX) (room hZ) (fun i j h => (hs i j x hX y hY).ne (congrArg (fun z => ‖Theater.out z‖) h)), hZ⟩
end spatial
local notation "FC" => Canon.FarCoefficients A

include H
include hK hx in
/-- The Near-coefficient tariff, bounded on the static compact, not merely power-log. -/
theorem demand_opeCoeff (u : Scan G n) (q : Q G) (k : ℕ) :
    ∃ C : ℝ, ∀ x ∈ K, ‖coeff k (FC u x q)‖ ≤ C :=
  hK.exists_bound_of_continuousOn (((H.far u).2.1 q k).mono hx)

include hS hy in
/-- (F.1), coefficientwise through p. -/
theorem demand_singleton (v : Scan G m) (q : Q G) (p : ℕ) :
    ChargeP (p+1) ((heft q : ℝ) + (totalG v : ℝ))
      (fun (y : ↥S) s => lonelyG (install A) (squeeze (-s) y.val) q v) :=
  Enh.Uniform.teeth_P H.scope H.dimensions hS hy H.awake v q (p+1)

include hK hx hS hy
/-- (F.O), through p and output horizon h. -/
theorem demand_ope (u : Scan G n) (v : Scan G m) (p h : ℕ) :
    RangeP (install A) K S u v (FC u) h 1 (p+1) :=
  (H.far u).2.2 K hK hx h (p+1) m S v hS hy

/-- Price the full correlation including its homogeneous Far weight W(v). -/
theorem demand_full (u : Scan G n) (v : Scan G m) (p h : ℕ) :
    ChargeP (p+1) (totalG v : ℝ) (fun (i : ↥K × ↥S) s =>
      party (install A) i.1.val (squeeze (-s) i.2.val) u v) := by
  -- No need for `h` to relate to the input caps.
  have key (i : ↥K × ↥S) (s : ℝ) :
      party (install A) i.1.val (squeeze (-s) i.2.val) u v =
        Basket (install A) u v (FC u i.1.val) h i.1.val (squeeze (-s) i.2.val) +
        Lamp (install A) h (squeeze (-s) i.2.val) v (FC u i.1.val) := by
    rw [Basket, sub_add_cancel]
  -- use FC, F.O & F.1
  simp_rw [key]; refine ChargeP.plus
    (ChargeP.grow (a:=(h:ℝ)+1+(totalG v:ℝ)) (demand_ope H hK hx hS hy u v p h)
      (by linarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h)])) ?_
  unfold Lamp Settle; refine ChargeP.sum _ fun j _ => ChargeP.sum _ fun b _ => ?_
  refine ChargeP.times (f:=fun (i : ↥K × ↥S) _ => FC u i.1.val (own b)) (fun k _ => ?_) ?_
  · obtain ⟨C,hC⟩ := demand_opeCoeff H hK hx u (own b) k
    exact Rain.cash ⟨C, fun i => hC i.1.val i.1.property⟩
  · exact ChargeP.pull (ChargeP.grow (demand_singleton H hS hy v (own b) p)
      (show (totalG v : ℝ) ≤ _ from le_add_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) _))) Prod.snd

end YM.FVA2.GradedFar
