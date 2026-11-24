import YM.Integration.WilsonMixedFreshMerger
import YM.QuadraticLocal.Germ.Cabin

/-! Carry the complete test collar of the elected pre-canopy through an unmasked birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedFreshMergerCrown
open Function Finset Lattice Wilson RG Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal
open QuadraticLocal.Affinity QuadraticLocal.Canopy WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V I J E : Type} [DecidableEq V] {R : Census V}
  {o : V → Site n} {films : V → Type} [∀ v, AddCommGroup (films v)] [∀ v, Module ℝ (films v)]
  (actors : ∀ v, Set (films v)) (pieces : ∀ v, Submodule ℝ (films v))
  (lands : V → Support n) {p : BudgetPoint}

omit [∀ v, AddCommGroup (films v)] [∀ v, Module ℝ (films v)] in
private theorem value (L : Lamps (Wallet actors) I G p o R) (t : Wallet actors) (i : I) (U : Config G n) :
    gap L.shade t i U = if L.clear i ∨ Healthy p.threshold (L.ground i) U then 0 else L.nominal t i U := by
  by_cases simple : L.clear i
  · simp [gap, Lamps.light, Lamps.shade, simple]
  by_cases healthy : Healthy p.threshold (L.ground i) U
  · change (if L.clear i then _ else masked p.threshold (L.ground i) (L.shade.nominal t i) U) - _ = _
    rw [if_neg simple, masked_eq _ _ _ _ healthy, sub_self, if_pos (Or.inr healthy)]
  change (if L.clear i then _ else masked p.threshold (L.ground i) (L.shade.nominal t i) U) - _ = _
  rw [if_neg simple, masked_ne _ _ _ _ healthy, zero_sub, if_neg (not_or.mpr ⟨simple, healthy⟩)]
  change - -L.nominal t i U = L.nominal t i U
  exact neg_neg _

theorem enrolled (L : Lamps (Wallet actors) I G p o R) (file : Taut lands actors pieces L)
    (i : I) (U : Config G n) :
    Stencil lands actors pieces ((sheet L.shade).place i).val (fun t => (sheet L.shade).soap t i U) := by
  constructor
  intro s
  change Addressable lands actors pieces (L.ground i) s.val
    (fun t => (Poly.send (L.mode i) (gap L.shade t i U)).part s)
  simp_rw [value, Poly.part_send]
  split
  · next same =>
    subst s
    split
    · exact Addressable.gone
    · exact ⟨file.adv i U,fun _ _ v hv => file.house i v hv⟩
  · exact Addressable.gone

/-- Use with Cabin.attentive on the actual mid-point of the very same Travel.Walk. -/
theorem posted [Countable J] [Countable I] {P : Rep G n} {A : Activities G n} {e f a c : ℝ}
    (H : Hard (Wallet actors) P.p A.forced A.K o R)
    (D : Kiosk.Second P.p A P.activities e f a c)
    (S : Lamps (Wallet actors) E G P.p o R) (L : Lamps (Wallet actors) I G P.p o R)
    (M : ShiftRows (Wallet actors) J G P.p o R)
    (hard : Crown lands actors pieces H) (store : Taut lands actors pieces S)
    (fresh : Taut lands actors pieces L)
    (attached : ∀ j U, Stencil lands actors pieces (M.place j).val (fun t => M.soap t j U)) :
    Collared lands actors pieces P
      (⟨L.join S,Kiosk.Second.canopy H (roll M L.shade) D⟩ : Gallery (Wallet actors) (I ⊕ E) o P R) := by
  refine ⟨?_, Crown.second H D (roll M L.shade) hard ?_⟩
  · constructor
    · rintro (i | i)
      · exact fresh.house i
      · exact store.house i
    · rintro (i | i)
      · exact fresh.adv i
      · exact store.adv i
  intro j U
  cases j with
  | inl j => exact attached j U
  | inr i => exact enrolled actors pieces lands L fresh i U

end YM.Integration.WilsonMixedFreshMergerCrown
