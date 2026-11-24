import YM.Integration.ReaderFiniteExtraction
import YM.Integration.FiniteHorizonGram

/-!
The original Reader in the original running physical frame. The finite probe
inverse is supplied by actual leading convergence, and hence costs one fixed
constant near zero. No numerical realization of a formal MS field conversion
and no uniform inverse hypothesis are introduced here.

The moving physical probes and their two scalar residuals remain explicit.
A fixed-macroscopic-exterior OPE estimate does not by itself supply those
residuals at the moving, `J r`-valued probes.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ReaderRunningExtraction
open Set Filter Function Spec Climb PhysMS OPE OPE.Orbits Trace.Pilot
open FiniteHorizonGram
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J)

include H in
/-- One actual inverse constant before every output grade through `D`, every
physical field and every candidate in the original free coordinates. -/
lemma finite_coefficient_error (D : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ (m : ℕ), m ≤ D →
      ∀ (v : S.Field m) (w : (Bel C.book).Field m),
        ‖(J r m).symm v - w‖ ≤
          K * ‖physicalProbes m (J r) r v - runningProbes m (J r) r w‖ := by
  choose K hK hp using fun m : Fin (D + 1) => coefficient_error F m.val J H
  let total : ℝ := ∑ m, K m
  have hle (m : Fin (D + 1)) : K m ≤ total :=
    Finset.single_le_sum (fun n _ => zero_le_one.trans (hK n)) (Finset.mem_univ m)
  refine ⟨total, (hK ⟨0, Nat.zero_lt_succ D⟩).trans (hle _), ?_⟩
  filter_upwards [eventually_all.mpr hp] with r hr m hm v w
  let q : Fin (D + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  exact (hr q v w).trans (mul_le_mul_of_nonneg_right (hle q) (norm_nonneg _))

variable {I : Type} [Fintype I] {d : I → ℕ}

/-- Literal pullback of the original real, rotation-averaged Reader field.
With `v = PhysMS.Frame.born J r u`, this is the existing `Frame.row` body. -/
def pulledFresh (m : ℕ) (x : I → E4) (v : Labels S d) (o : E4) (r : ℝ) :
    (Bel C.book).Field m :=
  (J r m).symm (R.fresh m x o v)

/-- Every sufficient packet horizon gives the same pulled-back original field. -/
lemma pulled_packet (m D : ℕ) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) (r : ℝ) :
    (J r m).symm (R.cutTest m D (R.packet D x v o)) =
      pulledFresh F R J m x v o r := by
  rw [R.filtered_packet m D h]
  rfl

include H in
lemma fresh_error (D : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ (m : ℕ), m ≤ D →
      ∀ (x : I → E4) (v : Labels S d) (o : E4) (w : (Bel C.book).Field m),
        ‖pulledFresh F R J m x v o r - w‖ ≤
          K * ‖physicalProbes m (J r) r (R.fresh m x o v) -
            runningProbes m (J r) r w‖ := by
  obtain ⟨K, hK, hp⟩ := finite_coefficient_error F J H D
  exact ⟨K, hK, hp.mono fun r hr m hm x v o w => hr m hm (R.fresh m x o v) w⟩

include H in
/-- Same original packet, same `J`, and one constant for all retained grades;
the packet horizon may be increased after the constant has been fixed. -/
lemma packet_error (D : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ (m : ℕ), m ≤ D →
      ∀ (E : ℕ), m ≤ E →
      ∀ (x : I → E4) (v : Labels S d) (o : E4) (w : (Bel C.book).Field m),
        ‖pulledFresh F R J m x v o r - w‖ ≤
          K * ‖physicalProbes m (J r) r (R.cutTest m E (R.packet E x v o)) -
            runningProbes m (J r) r w‖ := by
  obtain ⟨K, hK, hp⟩ := fresh_error F R J H (d := d) D
  refine ⟨K, hK, hp.mono fun r hr m hm E hE x v o w => ?_⟩
  rw [R.filtered_packet m E hE]
  exact hr m hm x v o w

include H in
/-- Independent scalar residuals at the actual moving physical probes control
the coefficient vector without a further power of the length. -/
lemma fresh_two_residuals (D : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ (m : ℕ), m ≤ D →
      ∀ (x : I → E4) (v : Labels S d) (o : E4) (w : (Bel C.book).Field m)
        (actual : ProbeIndex C m → ℂ) (opeError matchingError : ℝ),
      0 ≤ opeError → 0 ≤ matchingError →
      (∀ i, ‖actual i - physicalProbes m (J r) r (R.fresh m x o v) i‖ ≤ opeError) →
      (∀ i, ‖actual i - runningProbes m (J r) r w i‖ ≤ matchingError) →
        ‖pulledFresh F R J m x v o r - w‖ ≤ K * (opeError + matchingError) := by
  obtain ⟨K, hK, hp⟩ := fresh_error F R J H (d := d) D
  refine ⟨K, hK, hp.mono fun r hr m hm x v o w actual e₁ e₂ h₁ h₂ ho hc => ?_⟩
  apply (hr m hm x v o w).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
  apply (pi_norm_le_iff_of_nonneg (add_nonneg h₁ h₂)).mpr
  intro i
  calc
    ‖physicalProbes m (J r) r (R.fresh m x o v) i - runningProbes m (J r) r w i‖ =
      ‖(actual i - runningProbes m (J r) r w i) -
        (actual i - physicalProbes m (J r) r (R.fresh m x o v) i)‖ := by
          congr 1; ring
    _ ≤ ‖actual i - runningProbes m (J r) r w i‖ +
      ‖actual i - physicalProbes m (J r) r (R.fresh m x o v) i‖ := norm_sub_le _ _
    _ ≤ e₂ + e₁ := add_le_add (hc i) (ho i)
    _ = e₁ + e₂ := add_comm _ _

open Asymptotics

include H in
/-- Finite moving-probe remainders preserve their little-o order in the
original running coordinates; the inverse bound is derived from `Leading`. -/
lemma fresh_two_residuals_isLittleO {α E : Type*} {l : Filter α}
    [SeminormedAddCommGroup E] (m : ℕ)
    (r : α → ℝ) (hr : Tendsto r l trail)
    (x : α → I → E4) (v : α → Labels S d) (o : α → E4)
    (w : α → (Bel C.book).Field m) (actual : α → ProbeIndex C m → ℂ)
    (scale : α → E)
    (ordinaryOPE : ∀ i, (fun a => actual a i -
      physicalProbes m (J (r a)) (r a) (R.fresh m (x a) (o a) (v a)) i) =o[l] scale)
    (completeProductMatch : ∀ i, (fun a => actual a i -
      runningProbes m (J (r a)) (r a) (w a) i) =o[l] scale) :
    (fun a => pulledFresh F R J m (x a) (v a) (o a) (r a) - w a) =o[l] scale := by
  let delta a := physicalProbes m (J (r a)) (r a) (R.fresh m (x a) (o a) (v a)) -
    runningProbes m (J (r a)) (r a) (w a)
  have hd : delta =o[l] scale := by
    apply Asymptotics.isLittleO_pi.mpr
    intro i
    apply ((completeProductMatch i).sub (ordinaryOPE i)).congr_left
    intro a
    dsimp only [delta, Pi.sub_apply]
    ring
  obtain ⟨K, _, hp⟩ := coefficient_error F m J H
  have hbound : (fun a => pulledFresh F R J m (x a) (v a) (o a) (r a) - w a) =O[l] delta := by
    apply Asymptotics.IsBigO.of_bound K
    exact (hr.eventually hp).mono fun a ha => ha (R.fresh m (x a) (o a) (v a)) (w a)
  exact hbound.trans_isLittleO hd

end YM.Integration.ReaderRunningExtraction
