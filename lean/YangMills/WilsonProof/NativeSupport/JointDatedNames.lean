import YangMills.WilsonProof.NativeSupport.InletColors
import YangMills.WilsonProof.NativeSupport.JointRootedInput
import YangMills.WilsonProof.NativeSupport.RelocatedPattern

/-! Both perturbations of each dated blocking bond have distinct permanent
names on the microscopic torus. The complete name budget, including unused
names, is uniform in its period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset Lattice Wilson RG RGComparison.Core16 YM.Pressure Extra.Multi Packet
open scoped BigOperators Classical
variable {n c : Side} {G : Gauge}

theorem home_lift (d : Descent n c) (x : Site c) : home d (liftSite d x)=x := by
  induction d with
  | nil => rfl
  | push S T d ih => exact (congrArg S.ratio.parent (ih _)).trans (S.ratio.embed_parent x)

def liftBond (d : Descent n c) (b : Bond c) : Bond n := (liftSite d b.1,b.2)

theorem liftBond_injective (d : Descent n c) : Injective (liftBond d) := by
  intro b k eq
  exact Prod.ext (by simpa only [liftBond,home_lift] using congrArg (fun b : Bond n => home d b.1) eq)
    (congrArg (fun x : Bond n => x.2) eq)

theorem fine_birth {A : Levels G} {per : ℕ} (T : Slices A per) {j N : ℕ} (hj : j<N)
    (b : Bond (A.S.side j per)) :
    home (traversal T hj) (liftBond (traversal T hj.le) b).1=(A.clock.op j per).ratio.embed b.1 := by
  rw [traversal_push T hj]
  exact home_lift (traversal T hj) _

theorem color_price (d : Descent n c) : Fintype.card (Color d)=scale d ^ 4*4 := by
  have paid := color_count d
  rw [← side_scale d, mul_pow, mul_assoc] at paid
  exact Nat.eq_of_mul_eq_mul_left (pow_pos c.pos _) paid

/-- A date can include a perturbation kind. The two booleans in `Ink`
are auxiliary colors which are removed after each original step. -/
theorem dated_occupancy {I J : Type} [Fintype I] [Fintype J]
    (d : Descent n c) (physical:I → Site n) :
    Occupancy (fun p : Painted.Ink (I ⊕ (J × Bond n)) =>
      home d (Sum.elim physical (fun s => s.2.1) p.1))
      ((Fintype.card I+Fintype.card J*(scale d^4*4))*4) := by
  classical
  intro x
  let code : Painted.Ink (I ⊕ (J × Bond n)) → (I ⊕ (J × Color d)) × Bool × Bool :=
    fun p => (p.1.map id (fun s => (s.1,(partition d s.2).2)),p.2)
  have inj : Set.InjOn code ↑(univ.filter (fun p : Painted.Ink (I ⊕ (J × Bond n)) =>
      home d (Sum.elim physical (fun s => s.2.1) p.1)=x)) := by
    rintro ⟨i,a⟩ hi ⟨j,b⟩ hj eq
    have ab : a=b := congrArg Prod.snd eq
    subst b
    have ij := congrArg Prod.fst eq
    simp only [mem_coe,mem_filter,mem_univ,true_and] at hi hj
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg (fun u : I => (Sum.inl u,a)) (Sum.inl.inj ij)
      | inr j => contradiction
    | inr i => cases j with
      | inl j => contradiction
      | inr j =>
        have kj : (i.1,(partition d i.2).2)=(j.1,(partition d j.2).2) := Sum.inr.inj ij
        have xx : (partition d i.2).1=(partition d j.2).1 :=
          (coordinates_parent d _).trans ((hi.trans hj.symm).trans (coordinates_parent d _).symm)
        have bb := (partition d).injective (Prod.ext xx (congrArg (fun u : J × Color d => u.2) kj))
        exact congrArg (fun u : J × Bond n => (Sum.inr u,a)) (Prod.ext (congrArg (fun u : J × Color d => u.1) kj) bb)
  calc
    _ ≤ (univ : Finset ((I ⊕ (J × Color d)) × Bool × Bool)).card :=
      card_le_card_of_injOn code (fun _ _=>mem_univ _) inj
    _ = _ := by rw [card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_prod, color_price, Fintype.card_prod, Fintype.card_bool]
end YM.Integration.InletSusceptibility
