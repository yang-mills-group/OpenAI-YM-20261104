import YM.Integration.QLocalNativeReaderPublication
import YM.Overlay.Pays
import YM.Extra.MULTISOURCE_BOUNDS.Bands

/-! Publish the native marked radial estimate at every independent scalar
test, using the old layout and the old forced activities. Each charge pays
the product of the original marker bills once. The signed density includes
the true quiet entry in each marked forced sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRadialPublication
open Finset Function Lattice Wilson RG Marker FVA1 Overlay Next.Foundations Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n} {V X : Type} [DecidableEq V] [Fintype V]
variable (a : Bands (YM.Stock.census V) P)

/-- Rescale each entire native mode, retaining its actual tags and supports. -/
def bands (a : Bands (YM.Stock.census V) P) (γ : V → ℂ) : Bands (YM.Stock.census V) P where
  origins := a.origins
  units := fun i => γ i * a.units i
  support := a.support
  rays := a.rays
  H := fun i => QlocalPageScaling.weight γ (a.rays i) • a.H i
  marks := a.marks
  entries := fun i j => QlocalPageScaling.weight γ (a.marks i j) • a.entries i j

theorem active (ha : a.Active) (γ : V → ℂ) : (bands a γ).Active where
  proper := ha.proper
  pins := ha.pins
  occurs := ha.occurs
  regular i := regular_smul _ (ha.regular i)
  retained i j hne := ha.retained i j (by
    intro h0
    apply hne
    change QlocalPageScaling.weight γ (a.marks i j) • a.entries i j = 0
    rw [h0, smul_zero])
  inspects i j U W h1 h2 := congrArg (_ * ·) (ha.inspects i j U W h1 h2)
  keeps i j U hne := ha.keeps i j U (by
    intro h0
    apply hne
    change _ * a.entries i j U = 0
    rw [h0, mul_zero])
  meas i j := (ha.meas i j).const_smul _
  invi i j t U := congrArg (_ * ·) (ha.invi i j t U)

private theorem weight_le (γ : V → ℂ) (M : V → ℝ) (hγ : ∀ i, ‖γ i‖ ≤ M i) (q : (YM.Stock.census V).Mode) :
    ‖QlocalPageScaling.weight γ q‖ ≤ Poly.toll M q := by
  rw [QlocalPageScaling.weight, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hγ i)

private theorem paid {I : Type} {w u M : V → ℝ} (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 ≤ M i)
    (cap : ∀ i, w i * M i ≤ u i) (s : I → Support n) (q : I → (YM.Stock.census V).Mode)
    (b : I → ℝ) (hb : ∀ i, 0 ≤ b i) (v : V) {p : BudgetPoint} {c : ℝ}
    (h : SumBudget (fun i => if v ∈ (q i).val then Poly.toll u (q i) * p.mass (s i) (b i) else 0) c) :
    SumBudget (fun i => if v ∈ (q i).val then Poly.toll w (q i) *
      p.mass (s i) (Poly.toll M (q i) * b i) else 0) c := by
  apply budget_mono h
  · intro i
    split
    · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (Finset.prod_nonneg fun j _ => hm j) (hb i)))
    · rfl
  · intro i
    split
    · have ht : Poly.toll w (q i) * Poly.toll M (q i) ≤ Poly.toll u (q i) := by
        unfold Poly.toll
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod (fun j _ => mul_nonneg (hw j).le (hm j)) (fun j _ => cap j)
      calc
        _ = (Poly.toll w (q i) * Poly.toll M (q i)) * p.mass (s i) (b i) := by unfold BudgetPoint.mass; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ht (mul_nonneg (Real.exp_nonneg _) (hb i))
    · rfl

/-- Common majorants precede every tested regular and forced coefficient.
The original radial regular and forced totals and its separate unit charge
are preserved under the paid change of radii. -/
theorem common {u w M : V → ℝ} (hw : ∀ i, 0 < w i) (hM : ∀ i, 0 ≤ M i)
    (cap : ∀ i, w i * M i ≤ u i) {U C D b : ℝ} (hr : a.Radial u U C D b)
    (γ : X → V → ℂ) (hγ : ∀ x i, ‖γ x i‖ ≤ M i) :
    ∃ t : ℕ → ℝ, ∃ h : ℕ × ℕ → ℝ, ∃ g : V → ℝ,
      (∀ i, 0 ≤ t i ∧ ∀ x v, v ∈ (a.rays i).val → P.p.supBounds (a.origins v) (a.support i)
        ((bands a (γ x)).H i) (t i)) ∧
      (∀ v, SumBudget (fun i => if v ∈ (a.rays i).val then
        Poly.toll w (a.rays i) * P.p.mass (a.support i) (t i) else 0) C) ∧
      (∀ i j, 0 ≤ h (i,j) ∧ ∀ x z, ‖(bands a (γ x)).entries i j z‖ ≤ h (i,j)) ∧
      (∀ v, SumBudget (fun k : ℕ × ℕ => if v ∈ (a.marks k.1 k.2).val then
        Poly.toll w (a.marks k.1 k.2) * P.p.mass (P.activities.forced k.1).support (h k) else 0) (D*b)) ∧
      (∀ v, 0 ≤ g v ∧ (∀ x, ‖(bands a (γ x)).units v‖ ≤ g v) ∧ w v * g v ≤ U) := by
  obtain ⟨t, ht, htpay⟩ := hr.bulk
  obtain ⟨b', hb', hbpay⟩ := hr.hits
  let H (q : (YM.Stock.census V).Mode) := Poly.toll M q
  have Hnn (q : (YM.Stock.census V).Mode) : 0 ≤ H q := Finset.prod_nonneg fun i _ => hM i
  refine ⟨fun i => H (a.rays i) * t i, fun k => H (a.marks k.1 k.2) * b' k,
    fun v => M v * ‖a.units v‖, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨mul_nonneg (Hnn _) (ht i).1, ?_⟩
    intro x v hv
    have h := bound_smul (QlocalPageScaling.weight (γ x) (a.rays i)) ((ht i).2 v hv)
    have he := mul_le_mul_of_nonneg_right (weight_le (γ x) M (hγ x) (a.rays i)) (ht i).1
    exact ⟨h.1.trans he, fun z hz l hl hD => (h.2 z hz l hl hD).trans he⟩
  · exact fun v => paid hw hM cap a.support a.rays t (fun i => (ht i).1) v (htpay v)
  · intro i j
    refine ⟨mul_nonneg (Hnn _) (hb' i j).1, ?_⟩
    intro x z
    change ‖QlocalPageScaling.weight (γ x) _ * a.entries i j z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (weight_le (γ x) M (hγ x) _) ((hb' i j).2 z) (norm_nonneg _) (Hnn _)
  · exact fun v => paid hw hM cap _ _ b' (fun i => (hb' i.1 i.2).1) v (hbpay v)
  · intro v
    refine ⟨mul_nonneg (hM v) (norm_nonneg _), fun x => ?_, ?_⟩
    · change ‖γ x v * a.units v‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hγ x v) (norm_nonneg _)
    · rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (cap v) (norm_nonneg _)).trans (hr.localU v)

theorem tested_radial {u w M : V → ℝ} (hw : ∀ i, 0 < w i) (hM : ∀ i, 0 ≤ M i)
    (cap : ∀ i, w i * M i ≤ u i) {U C D b : ℝ} (hr : a.Radial u U C D b)
    (γ : X → V → ℂ) (hγ : ∀ x i, ‖γ x i‖ ≤ M i) (x : X) : (bands a (γ x)).Radial w U C D b := by
  obtain ⟨t, h, g, ht, hb, hh, hf, hu⟩ := common a hw hM cap hr γ hγ
  exact ⟨hw, fun v => (mul_le_mul_of_nonneg_left ((hu v).2.1 x) (hw v).le).trans (hu v).2.2,
    hr.factor, ⟨t, fun i => ⟨(ht i).1, (ht i).2 x⟩, hb⟩,
    ⟨h, fun i j => ⟨(hh i j).1, (hh i j).2 x⟩, hf⟩⟩

private theorem same_pass (γ : V → ℂ) (z : Poly (YM.Stock.census V)) :
    NativeWeightedColors.fuse id γ (Poly.pass z) = Poly.pass (NativeWeightedColors.fuse id γ z) := by
  have hp (k : ℕ) : NativeWeightedColors.fuse id γ (z^k) = (NativeWeightedColors.fuse id γ z)^k := by
    induction k with
    | zero => simpa only [pow_zero] using NativeWeightedColors.fuse_one id γ
    | succ k ih => rw [pow_succ, NativeWeightedColors.fuse_mul, ih, pow_succ]
  unfold Poly.pass
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, hp]

/-- The full admissible packets, including the unscaled original vacuum K,
commute with the same marker map as the signed regular log. -/
theorem density (γ : V → ℂ) (ha : a.Active) {w : V → ℝ} {u c d b δ κ : ℝ}
    (hr : a.Radial w u c d b) (hP : P.activities.Valid P.p δ κ) (U : Config G n) :
    NativeWeightedColors.fuse id γ (a.density U) = (bands a γ).density U := by
  let F := NativeWeightedColors.fuse id γ
  have hgl (i : V) : F (Poly.send ((YM.Stock.census V).fire i) (a.units i)) =
      Poly.send ((YM.Stock.census V).fire i) ((bands a γ).units i) := by
    rw [show F = NativeWeightedColors.fuse id γ from rfl, QlocalPageScaling.fuse_send]
    simp [bands, QlocalPageScaling.weight, Census.fire]
  have hreg (i : ℕ) : F (a.ray i U) = (bands a γ).ray i U := by
    unfold Bands.ray
    rw [show F = NativeWeightedColors.fuse id γ from rfl, QlocalPageScaling.fuse_send]
    by_cases h : Healthy P.p.threshold (a.support i) U <;> simp [bands, masked, h]
  have hlog : F (a.extra U) = (bands a γ).extra U := by
    unfold Bands.extra
    rw [map_add, map_sum, F.map_tsum (a.bulkBound ha hr U).1]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun i _ => hgl i)) (tsum_congr hreg)
  have hforce (i : ℕ) : F (a.each i U) = (bands a γ).each i U := by
    unfold Bands.each
    rw [map_add, F.map_tsum ((a.baseBound ha hr hP U).1 i)]
    apply congrArg₂ (· + ·)
    · rw [show F = NativeWeightedColors.fuse id γ from rfl, QlocalPageScaling.fuse_send]
      simp [QlocalPageScaling.weight, Census.quiet]
    · exact tsum_congr (fun j => QlocalPageScaling.fuse_send γ _ _)
  have hpacket (t : Finset ℕ) : F (a.packet t U) = (bands a γ).packet t U := by
    unfold Bands.packet
    split
    · rw [show F = NativeWeightedColors.fuse id γ from rfl, NativeWeightedColors.fuse_prod]
      exact Finset.prod_congr rfl (fun i _ => hforce i)
    · exact map_zero _
  have hcluster : F (a.cluster U) = (bands a γ).cluster U := by
    unfold Bands.cluster
    rw [F.map_tsum (a.population ha hr hP U).1]
    exact tsum_congr hpacket
  unfold Bands.density
  rw [map_smul, NativeWeightedColors.fuse_mul, same_pass, hlog, hcluster]

open FVA1 PhysicalNext.Repeat.Legato Extra.Histories Extra.Trajectories RG3.Script.Picnic MergeProof.Accent
open LocalComparison ComparisonDensity.Address

/-- The untested selected physical representation suffices for the entire
independent family on the same Run, at the same native outgoing Rep. -/
theorem actual {O : Run G} {p L k : ℕ} {hk : k ≤ L} [Nonempty V]
    (I : ActualRunQlocalNativeTuple.Datum O p L k hk V) (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, O.family.ref (ActualRunQlocalNativeTuple.grade I i) ≤ L)
    {m : ℕ} (hm : m ≤ L) (A : Bands (YM.Stock.census V) (O.family.path.rep N p m)) (hA : A.Active)
    {w : V → ℝ} {u c d b : ℝ} (hr : A.Radial w u c d b)
    (he : ∀ U, A.density U = gust O.family.path N p L (QLocalNativeReaderPublication.source I N) m hm U)
    (x : IndependentTests (ActualRunQlocalNativeTuple.orbit I)) (U : Config G (O.family.side m p)) :
    (bands A (QLocalNativeReaderPublication.coefficients I x)).density U =
      gust O.family.path N p L ((ActualRunQlocalNativeTuple.input I hG N hL).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit I) x)).density m hm U := by
  rw [QLocalNativeReaderPublication.history I hG N hL href x hm]
  change _ = NativeWeightedColors.fuse id _ (gust O.family.path N p L _ m hm U)
  rw [← he U]
  exact (density A _ hA hr (O.makes.wilson.represents N p m (hm.trans hL)).good.labels U).symm

end YM.Integration.QLocalRadialPublication
end
