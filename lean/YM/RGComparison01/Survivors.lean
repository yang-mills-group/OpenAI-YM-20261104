import YM.RGComparison01.LogSplit

/-!
# What survived the `Beacon` cut?

Here nonzero log kernels among kept component terms. In particular no
seed, no reads of selected old K vertices, and quantitative span cost
of the support. Not asserting a fixed number of labels at that cut.

Mind: The diameter bound implied by our cover bound can be too coarse
to pass *all* survivors into a common analytic box at fixed relative
size. In particular ratio/chain and rough-E terms will need separate care.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open PhysicalNext PhysicalNext.Repeat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace Survivors
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ s α : ℝ}
    {χ : Chi} {H : Cash W s μ L Q o α T R} {ℓ : ℕ}

lemma noSeed (p : H.ThinP) (ht : troupe T R Q.halo (radiusB s) p.val) (hu : Cash.numP p.val < 1) :
    p.val.toLeft=∅ ∧ own p.val=∅ := by
  have he : p.val.toLeft=∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨i,hi⟩ => by
    have hx : 1 ≤ i.shares := by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (ht.1.checkpoints i hi).1
    apply Nat.not_lt.mpr ?_ hu
    exact hx.trans (Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi))
  refine ⟨he,Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨i,hi⟩; obtain ⟨j,hj⟩ := (R.activities.forced i).inventory_ne
  obtain ⟨z,hy,_⟩ := ht.2.2 _ hi _ hj
  unfold roster Packets.store at hy; rw [he] at hy; simp at hy

lemma shape_covers {p : H.ThinP} (h : Ac.Spark H.supportP p.val) :
    (coverNumber (radiusB s) (H.smallAt p):ℝ) ≤ H.shapeW p.val := by
  calc
    _ ≤ ∑ i ∈ p.val,(coverNumber (radiusB s) (H.supportP i):ℝ) := by exact_mod_cast Ac.cover _ _ h
    _ ≤ _ := sum_le_sum fun i _ => le_add_of_nonneg_right (show 0 ≤ Mixed.lengths S H.faresP
      (ConnectedActivityE6.lengths T R) i from (by
        rcases i with i|i
        · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
        exact H.armed.extra _))

/-- Limit the residual obligation. These tests are direct on the component
log kernels. Selectors at `plusone` keep seats and references (`furrow`). -/
lemma survives {z : H.fragrances} (hh : ¬ Beacon.Exceptional H ℓ z)
    (V : Config G c) (he : stream H χ V z ≠ 0) :
    z.1 + 1 < ℓ ∧ Height.breadth H z < ℓ ∧
    (coverNumber (radiusB s) (Captain.reachability (H:=H) z) : ℝ) <
      (ℓ : ℝ)*Pressure.Stores.till s ∧
    ∀ j, let i := z.2 j
         i.val.toLeft=∅ ∧ own i.val=∅ ∧ Ac.Spark H.supportP i.val ∧
           troupe T R Q.halo (radiusB s) i.val := by
  have ht := not_or.mp hh
  have hu := not_or.mp ht.2
  have hb : Height.breadth H z < ℓ := lt_of_le_of_lt (Nat.le_add_left ..) (lt_of_not_ge ht.1)
  have hv (j) : leaflet H χ V (z.2 j) ≠ 0:= fun h => he (by
    unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ j) h,mul_zero,zero_div])
  have hz j : Ac.Spark H.supportP (z.2 j).val ∧ troupe T R Q.halo (radiusB s) (z.2 j).val := by
    by_contra hy
    apply hv j
    unfold leaflet likely
    simp_rw [Height.vacuity V (z.2 j) hy,sum_const_zero,mul_zero]
  have hk j : 1 ≤ (z.2 j).val.card:= Finset.card_pos.mpr (hz j).1.1
  refine ⟨lt_of_le_of_lt (le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _ => hk i))) hb, hb, ?_, ?_⟩
  · simp
  · apply lt_of_le_of_lt ?_ (lt_of_not_ge hu.2); unfold Height.depth
    apply le_trans ?_ (sum_le_sum (s:=univ) (fun i _=> shape_covers (hz i).1))
    have hpos := connected_pay H.seam H.smallAt (radiusB s) H.testS z.2 zero_le_one (by
      intro h; apply he; unfold stream Gas.term; rw [h,zero_mul,zero_div])
    unfold Trees.currency at hpos; simp_rw [one_mul,← Real.exp_sum, Real.exp_le_exp] at hpos
    exact hpos
  intro j i
  have hx : Cash.numP i.val < 1 := lt_of_le_of_lt (single_le_sum (f:=fun j => Cash.numP (z.2 j).val)
    (fun _ _=> Nat.zero_le _) (mem_univ j)) (lt_of_not_ge hu.1)
  obtain ⟨h₀,h₁⟩ := noSeed i (hz j).2 hx
  exact ⟨h₀,h₁,hz j⟩
end Survivors
end YM.RGComparison01
