import YM.Integration.NativeWeightedColors
import YM.Integration.NativeForcedPolynomialReentry
import YM.Integration.ActualRunFullPages

/-! Exact coefficient scaling of the original finite Page family.  The
Nat-indexed old gas is retained; its native finite-field identity justifies
transport by the existing full polynomial map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QlocalPageScaling
open Finset Function MeasureTheory Lattice Wilson RG Marker FVA1
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG3.Annuncia Planned.GuardedAtom PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V]

abbrev weight (γ : V → ℂ) (s : (Stock.census V).Mode) : ℂ :=
  ∏ i ∈ s.val, γ i

private def liftMode (s : (Stock.census V).Mode) :
    (Replica (id : V → V) (Stock.census V)).Mode :=
  ⟨s.val, mem_filter.mpr ⟨mem_univ _, ⟨by simp,
    fun _ _ _ _ h => h⟩⟩⟩

/-- The identity-fibre map multiplies one mode by precisely its marker product. -/
theorem fuse_send (γ : V → ℂ) (s : (Stock.census V).Mode) (c : ℂ) :
    NativeWeightedColors.fuse id γ (Poly.send s c) =
      Poly.send s (weight γ s * c) := by
  let a := liftMode s
  have hs : (NativeWeightedColors.keep (id : V → V)).share a = s := by
    apply Subtype.ext
    change s.val.image (id : V → V) = s.val
    exact Finset.image_id
  have hr : (NativeWeightedColors.keep (id : V → V)).restriction
      (Poly.send s c) = Poly.send a c := by
    rw [← hs]
    apply Marker.Poly.ext
    intro j
    change (Poly.send _ c).part ((NativeWeightedColors.keep id).share j) = _
    simp only [Poly.part_send, (NativeWeightedColors.keep id).inj.eq_iff]
  change Replica.mouth id (Stock.census V) γ
    ((NativeWeightedColors.keep id).restriction (Poly.send s c)) = _
  rw [hr, Replica.mouth_apply, Replica.puts]
  have hb : Replica.bill id (Stock.census V) a = s := by
    apply Subtype.ext
    simp [Replica.bill, a, liftMode]
  rw [hb]
  rfl

theorem fuse_part (γ : V → ℂ) (p : Poly (Stock.census V))
    (s : (Stock.census V).Mode) :
    (NativeWeightedColors.fuse id γ p).part s = weight γ s * p.part s := by
  have h := congrArg (fun z : Poly (Stock.census V) =>
    (NativeWeightedColors.fuse id γ z).part s) (Poly.studs p)
  simpa [map_sum, Poly.part_sum, fuse_send, Poly.part_send] using h.symm

variable {G : Gauge} {n : Side} {P : Rep G n}

private theorem fuse_aroma (γ : V → ℂ) (q : Page (Stock.census V) P)
    (U : Config G n) :
    NativeWeightedColors.fuse id γ (q.aroma 1 U) =
      q.aroma (weight γ q.s) U := by
  unfold Page.aroma
  cases q.shellx with
  | inl s => simp only [Sum.elim_inl, Page.point, one_mul, fuse_send]
  | inr k => exact map_zero _

private theorem fuse_payment (γ : V → ℂ) (q : Page (Stock.census V) P)
    (U : Config G n) (i : ℕ) :
    NativeWeightedColors.fuse id γ (q.payment 1 U i) =
      q.payment (weight γ q.s) U i := by
  unfold Page.payment
  cases q.shellx with
  | inl s => exact map_zero _
  | inr k =>
    simp only [Sum.elim_inr]
    split_ifs
    · simp only [Page.point, one_mul, fuse_send]
    exact map_zero _

private theorem fuse_rebook (γ : V → ℂ)
    (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census V)) (i : ℕ) (U : Config G n) :
    NativeWeightedColors.fuse id γ (NativeForcedPolynomialReentry.rebook K F i U) =
      NativeForcedPolynomialReentry.rebook K
        (fun s U => NativeWeightedColors.fuse id γ (F s U)) i U := by
  by_cases hi : i ∈ Set.range (cart K)
  · obtain ⟨s, rfl⟩ := hi
    rw [NativeForcedPolynomialReentry.at_address,
      NativeForcedPolynomialReentry.at_address]
  rw [NativeForcedPolynomialReentry.off_address K F hi,
    NativeForcedPolynomialReentry.off_address K _ hi]
  exact map_zero _

/-- Apply the native gas-to-field identity on both sides to transport the sum. -/
theorem fuse_gas (γ : V → ℂ) (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census V))
    {e k : ℝ} (hP : P.activities.Valid P.p e k)
    (hF : ∀ s, ¬ Sure s → F s = 0) (U : Config G n) :
    NativeWeightedColors.fuse id γ (NativeForcedPolynomialReentry.gas K F U) =
      NativeForcedPolynomialReentry.gas K
        (fun s U => NativeWeightedColors.fuse id γ (F s U)) U := by
  have hz : ∀ s, ¬ Sure s →
      (fun U => NativeWeightedColors.fuse id γ (F s U)) = 0 := by
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
  exact NativeWeightedColors.fuse_bead id γ _

variable {I : Type} [Fintype I]

/-- Exact finite Page scaling with the same old activity array and support flags. -/
theorem fuse_essence (γ : V → ℂ) (q : I → Page (Stock.census V) P)
    (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly (Stock.census V))
    {e k : ℝ} (hP : P.activities.Valid P.p e k)
    (hF : ∀ s, ¬ Sure s → F s = 0)
    (hPay : ∀ U i, (∑ j, (q j).payment 1 U i) =
      NativeForcedPolynomialReentry.rebook K F i U)
    (U : Config G n) :
    NativeWeightedColors.fuse id γ (essence q (fun _ => 0) (fun _ => 1) U) =
      essence q (fun _ => 0) (fun j => weight γ (q j).s) U := by
  have hPay' (i : ℕ) : (∑ j, (q j).payment (weight γ (q j).s) U i) =
      NativeForcedPolynomialReentry.rebook K
        (fun s U => NativeWeightedColors.fuse id γ (F s U)) i U := by
    rw [← fuse_rebook γ K F i U, ← hPay U i, map_sum]
    exact Finset.sum_congr rfl (fun j _ => (fuse_payment γ (q j) U i).symm)
  have hQuiet : (∑ j, (q j).aroma 1 U).part (Stock.census V).quiet = 0 := by
    rw [Poly.part_sum]
    apply Finset.sum_eq_zero
    intro j _
    unfold Page.aroma
    cases he : (q j).shellx with
    | inl s =>
      simp only [Sum.elim_inl, Page.point, Poly.part_send]
      exact if_neg (fun h => (q j).marked.ne_empty (congrArg Subtype.val h.symm))
    | inr k => rfl
  have hm : Mach (Stock.census V) (fun _ : V => (0 : ℂ)) = 0 := by simp [Mach]
  unfold essence
  simp only [hm, zero_add]
  simp_rw [hPay, hPay']
  change NativeWeightedColors.fuse id γ
    ((Real.exp (P.exponent U) : ℂ) •
      (Poly.pass (∑ j, (q j).aroma 1 U) * NativeForcedPolynomialReentry.gas K F U)) = _
  rw [map_smul, NativeWeightedColors.fuse_mul,
    NativeWeightedColors.fuse_pass id γ _ hQuiet, map_sum,
    fuse_gas γ K F hP hF U]
  simp_rw [fuse_aroma]
  rfl

/-- Actual Run specialization: the weighted full Page family is the complete
original-vacuum birth of the correspondingly scaled source kernels. -/
theorem actual_essence (R : Run G) (hG : G.Simple) (N p L : ℕ) (hL : L ≤ N)
    (o : Positions V (R.family.side L p)) (d : V → ℕ)
    (v : ∀ i, R.family.label (d i)) (href : ∀ i, R.family.ref (d i) ≤ L)
    (γ : V → ℂ) (U : Config G (R.family.side L p)) :
    essence (ActualRunFullPages.pages R hG N p L hL o d v) (fun _ => 0)
      (fun j => weight γ (ActualRunFullPages.pages R hG N p L hL o d v j).s) U =
    birth (Stock.census V) (R.family.path.rep N p L)
      (fun i W => γ i * ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i) W) U := by
  rw [← fuse_essence γ _ (OriginalForcedAddresses.actual_keeper R hG N L p hL)
    (ActualRunUnmaskedPartners.actualCorrection R N p L o d v)
    (R.makes.wilson.represents N p L hL).good.labels
    (NativeForcedPolynomialReentry.flow_zero _ o.origin
      (ActualRunUnmaskedPartners.actual_correction_flow R N p L o d v hL href))
    (ActualRunFullPages.payments R hG N p L hL o d v href) U,
    ActualRunFullPages.essence_full R hG N p L hL o d v href U]
  have h := congrFun (NativeWeightedColors.fuse_birth (id : V → V) γ
    (R.family.path.rep N p L)
    (fun i => ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i))) U
  simpa [ActualRunUnmaskedPartners.fullInput, ActualRunUnmaskedPartners.actualLog,
    JointSignedInitialization.Rooted.aggregate, birth] using h

end YM.Integration.QlocalPageScaling
