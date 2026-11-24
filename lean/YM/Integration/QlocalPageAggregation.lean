import YM.Integration.QlocalPageScaling

/-! Exact aggregation of finite native Pages through an arbitrary colour map.
Every original Page, support, payload and forced address is retained. A Page
using two alternatives of one output colour receives coefficient zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QlocalPageAggregation
open Finset Function MeasureTheory Lattice Wilson RG Marker FVA1
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG3.Annuncia Planned.GuardedAtom PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {V W : Type} [DecidableEq V] [Fintype V]
  [DecidableEq W] [Fintype W] (u : W → V)

def mode (s : (Stock.census W).Mode) : (Stock.census V).Mode :=
  ⟨s.val.image u, Finset.mem_univ _⟩

def weight (γ : W → ℂ) (s : (Stock.census W).Mode) : ℂ :=
  if Set.InjOn u (s.val : Set W) then ∏ i ∈ s.val, γ i else 0

/-- The complete colour map deletes exactly the repeated-colour modes. -/
theorem fuse_send (γ : W → ℂ) (s : (Stock.census W).Mode) (c : ℂ) :
    NativeWeightedColors.fuse u γ (Poly.send s c) =
      Poly.send (mode u s) (weight u γ s * c) := by
  by_cases h : Set.InjOn u (s.val : Set W)
  · let a : (Replica u (Stock.census V)).Mode :=
      ⟨s.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨Finset.mem_univ _, h⟩⟩⟩
    have hs : (NativeWeightedColors.keep u).share a = s := by
      apply Subtype.ext
      change s.val.image (id : W → W) = s.val
      exact Finset.image_id
    have hr : (NativeWeightedColors.keep u).restriction (Poly.send s c) =
        Poly.send a c := by
      rw [← hs]
      apply Marker.Poly.ext
      intro j
      change (Poly.send _ c).part ((NativeWeightedColors.keep u).share j) = _
      simp only [Poly.part_send, (NativeWeightedColors.keep u).inj.eq_iff]
    change Replica.mouth u (Stock.census V) γ
      ((NativeWeightedColors.keep u).restriction (Poly.send s c)) = _
    rw [hr, Replica.mouth_apply, Replica.puts]
    have hb : Replica.bill u (Stock.census V) a = mode u s := by
      apply Subtype.ext
      rfl
    rw [hb]
    simp only [weight, if_pos h]
    rfl
  · have hr : (NativeWeightedColors.keep u).restriction (Poly.send s c) = 0 := by
      apply Marker.Poly.ext
      intro j
      change (Poly.send s c).part ((NativeWeightedColors.keep u).share j) = 0
      rw [Poly.part_send]
      apply if_neg
      intro he
      have hv := congrArg Subtype.val he
      change j.val.image (id : W → W) = s.val at hv
      rw [Finset.image_id] at hv
      exact h (hv ▸ (Replica.admit u (Stock.census V) j).separate)
    change Replica.mouth u (Stock.census V) γ
      ((NativeWeightedColors.keep u).restriction (Poly.send s c)) = _
    rw [hr, map_zero]
    simp only [weight, if_neg h, zero_mul, Poly.send_zero]

variable {G : Gauge} {n : Side} {P : Rep G n}

def page (q : Page (Stock.census W) P) : Page (Stock.census V) P where
  s := mode u q.s
  marked := q.marked.image u
  shellx := q.shellx
  term := q.term
  chip := q.chip

private theorem fuse_aroma (γ : W → ℂ) (q : Page (Stock.census W) P)
    (U : Config G n) :
    NativeWeightedColors.fuse u γ (q.aroma 1 U) =
      (page u q).aroma (weight u γ q.s) U := by
  unfold Page.aroma
  cases he : q.shellx with
  | inl s =>
    simp only [page, he, Sum.elim_inl, Page.point, one_mul, fuse_send]
    simp only [Page.ready, he, Sum.elim_inl]
  | inr k => simp only [page, he, Sum.elim_inr, map_zero]

private theorem fuse_payment (γ : W → ℂ) (q : Page (Stock.census W) P)
    (U : Config G n) (i : ℕ) :
    NativeWeightedColors.fuse u γ (q.payment 1 U i) =
      (page u q).payment (weight u γ q.s) U i := by
  unfold Page.payment
  cases he : q.shellx with
  | inl s => simp only [page, he, Sum.elim_inl, map_zero]
  | inr k =>
    simp only [page, he, Sum.elim_inr]
    split_ifs
    · simp only [Page.point, one_mul, fuse_send]
      simp only [Page.ready, he, Sum.elim_inr]
    exact map_zero _

private theorem fuse_rebook (γ : W → ℂ)
    (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census W)) (i : ℕ) (U : Config G n) :
    NativeWeightedColors.fuse u γ (NativeForcedPolynomialReentry.rebook K F i U) =
      NativeForcedPolynomialReentry.rebook K
        (fun s U => NativeWeightedColors.fuse u γ (F s U)) i U := by
  by_cases hi : i ∈ Set.range (MergeProof.cart K)
  · obtain ⟨s, rfl⟩ := hi
    rw [NativeForcedPolynomialReentry.at_address,
      NativeForcedPolynomialReentry.at_address]
  rw [NativeForcedPolynomialReentry.off_address K F hi,
    NativeForcedPolynomialReentry.off_address K _ hi]
  exact map_zero _

private theorem fuse_gas (γ : W → ℂ) (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census W))
    {e k : ℝ} (hP : P.activities.Valid P.p e k)
    (hF : ∀ s, ¬ Sure s → F s = 0) (U : Config G n) :
    NativeWeightedColors.fuse u γ (NativeForcedPolynomialReentry.gas K F U) =
      NativeForcedPolynomialReentry.gas K
        (fun s U => NativeWeightedColors.fuse u γ (F s U)) U := by
  have hz : ∀ s, ¬ Sure s →
      (fun U => NativeWeightedColors.fuse u γ (F s U)) = 0 := by
    intro s hs
    funext U
    rw [hF s hs]
    exact map_zero _
  rw [NativeForcedPolynomialReentry.gas_eq K F hP (w := fun _ => 1)
      (fun _ => zero_lt_one) hF,
    NativeForcedPolynomialReentry.gas_eq K _ hP (w := fun _ => 1)
      (fun _ => zero_lt_one) hz,
    NativeWeightedColors.fuse_field]
  apply congrArg (fun f => field f (flags P.p.threshold U))
  funext s
  rw [map_add]
  congr 1
  exact NativeWeightedColors.fuse_bead u γ _

variable {I : Type} [Fintype I]

/-- Full finite Page aggregation preserves the original Nat-indexed gas. -/
theorem fuse_essence (γ : W → ℂ) (q : I → Page (Stock.census W) P)
    (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census W))
    {e k : ℝ} (hP : P.activities.Valid P.p e k)
    (hF : ∀ s, ¬ Sure s → F s = 0)
    (hPay : ∀ U i, (∑ j, (q j).payment 1 U i) =
      NativeForcedPolynomialReentry.rebook K F i U)
    (U : Config G n) :
    NativeWeightedColors.fuse u γ (essence q (fun _ => 0) (fun _ => 1) U) =
      essence (fun j => page u (q j)) (fun _ => 0)
        (fun j => weight u γ (q j).s) U := by
  have hPay' (i : ℕ) : (∑ j, (page u (q j)).payment (weight u γ (q j).s) U i) =
      NativeForcedPolynomialReentry.rebook K
        (fun s U => NativeWeightedColors.fuse u γ (F s U)) i U := by
    rw [← fuse_rebook u γ K F i U, ← hPay U i, map_sum]
    exact Finset.sum_congr rfl (fun j _ => (fuse_payment u γ (q j) U i).symm)
  have hQuiet : (∑ j, (q j).aroma 1 U).part (Stock.census W).quiet = 0 := by
    rw [Poly.part_sum]
    apply Finset.sum_eq_zero
    intro j _
    unfold Page.aroma
    cases he : (q j).shellx with
    | inl s =>
      simp only [Sum.elim_inl, Page.point, Poly.part_send]
      exact if_neg (fun h => (q j).marked.ne_empty (congrArg Subtype.val h.symm))
    | inr k => rfl
  have hmW : Mach (Stock.census W) (fun _ : W => (0 : ℂ)) = 0 := by simp [Mach]
  have hmV : Mach (Stock.census V) (fun _ : V => (0 : ℂ)) = 0 := by simp [Mach]
  unfold essence
  simp only [hmW, hmV, zero_add]
  simp_rw [hPay, hPay']
  change NativeWeightedColors.fuse u γ
    ((Real.exp (P.exponent U) : ℂ) •
      (Poly.pass (∑ j, (q j).aroma 1 U) * NativeForcedPolynomialReentry.gas K F U)) = _
  rw [map_smul, NativeWeightedColors.fuse_mul,
    NativeWeightedColors.fuse_pass u γ _ hQuiet, map_sum,
    fuse_gas u γ K F hP hF U]
  simp_rw [fuse_aroma]
  rfl

omit [Fintype I] in
/-- The actual original Page family yields the complete aggregated birth. -/
theorem actual_essence (R : Run G) (hG : G.Simple) (N p L : ℕ) (hL : L ≤ N)
    (o : Positions W (R.family.side L p)) (d : W → ℕ)
    (v : ∀ i, R.family.label (d i)) (href : ∀ i, R.family.ref (d i) ≤ L)
    (γ : W → ℂ) (U : Config G (R.family.side L p)) :
    essence (fun j => page u (ActualRunFullPages.pages R hG N p L hL o d v j))
      (fun _ => 0)
      (fun j => weight u γ (ActualRunFullPages.pages R hG N p L hL o d v j).s) U =
      birth (Stock.census V) (R.family.path.rep N p L)
        (JointSignedInitialization.Rooted.aggregate u γ
          (fun i => ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i))) U := by
  rw [← fuse_essence u γ _ (OriginalForcedAddresses.actual_keeper R hG N L p hL)
    (ActualRunUnmaskedPartners.actualCorrection R N p L o d v)
    (R.makes.wilson.represents N p L hL).good.labels
    (NativeForcedPolynomialReentry.flow_zero _ o.origin
      (ActualRunUnmaskedPartners.actual_correction_flow R N p L o d v hL href))
    (ActualRunFullPages.payments R hG N p L hL o d v href) U,
    ActualRunFullPages.essence_full R hG N p L hL o d v href U]
  have h := congrFun (NativeWeightedColors.fuse_birth u γ
    (R.family.path.rep N p L)
    (fun i => ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i))) U
  simpa only [ActualRunUnmaskedPartners.fullInput, ActualRunUnmaskedPartners.actualLog,
    birth] using h

end YM.Integration.QlocalPageAggregation
end
