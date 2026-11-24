import YM.Integration.ActualSignedMSReadout
import YM.Integration.SignedTensor

/-! A fixed-order criterion on the original grouped Wilson readout. A separate
cofinal set of legal (mesh, period) pairs is allowed for each basis tuple and
each outer configuration. The conclusion bounds every independent field tuple
at once in the native physical norm. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedUniformReadout
open Function Filter Set Spec OPE OPE.Orbits PhysMS Asymptotics
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open PhysicalMSOPECandidate ActualSignedMSReadout
open scoped Topology Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {n i D : ℕ}

/-- The complete Reader output, multilinear in its original independent fields. -/
def actualTensor (F : Final C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Fin n → E4) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i) (E C.labels D) :=
  (J r D).symm.toLinearMap.compMultilinearMap
    ((∑ k : Fin (D + 1),
      (F.sector.derivatives.rise (Nat.le_of_lt_succ k.isLt)).compMultilinearMap
        (Q.fresh k.val (d := fun _ : Fin n => i) x 0)).compLinearMap
          (fun _ => (J r i).toLinearMap))

theorem actualTensor_apply (F : Final C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Fin n → E4) (v : Fin n → E C.labels i) :
    actualTensor (D := D) F Q J r x v = actualOutput F Q J v r x := by
  simp only [actualTensor, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, _root_.sum_apply, actualOutput, Reader.packet,
    LinearEquiv.coe_coe]
  rfl

/-- The all-order conversion is applied first and the resulting polynomial is
truncated at the requested order. Each factor uses the fixed native basis. -/
def formalTensor (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t : ℝ) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i) (E C.labels D) :=
  ∑ k ∈ Finset.range (N + 1), (t : ℂ) ^ k •
    ∑ u : sheaf C.labels n i,
      ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
        (fun j => (RG11.Fields.tower C.labels i).b.coord (u j))).smulRight
          (∑ j : lab C.labels D, PowerSeries.coeff k (crown p Z B 0 u j) •
            (RG11.Fields.tower C.labels D).b j)

theorem formalTensor_apply (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t : ℝ) (v : Fin n → E C.labels i) :
    formalTensor p Z B N t v = composedTruncation p Z B v N t := by
  simp only [formalTensor, _root_.sum_apply, _root_.smul_apply,
    MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Module.Basis.coord_apply, composedTruncation,
    blockTruncation, blockCoefficient]

/-- Convergence of the actual grouped numerator means cofinal regulator bounds
suffice. The intermediate comparison level and its cutoff may vary throughout. -/
theorem remainder_iff_frequent_bound (F : Final C f S) (hS : Services C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hQ : Foundation F Q)
    (U : Detector S D) (v : Fin n → E C.labels i)
    (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
    (g : ℝ → ℝ) (hg : Trace.Pilot.Coupling G g) (hG : G.Simple)
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → Fin n → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : A → Blocks C.labels n i D) (N : ℕ)
    (level : (a : A) → (w : ℕ × ℕ) → Fin (w.1 + 1)) :
    ((fun a => actualOutput F Q J v (r a) (x a) -
      composedTruncation p Z (B a) v N (g (r a))) =o[l] (fun a => g (r a) ^ N)) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∃ᶠ w : ℕ × ℕ in f.fuse,
      ‖finiteReadout J U v (r a) (x a)
        (candidate J p Z (B a) v N (g (r a)) (r a))
        w.1 w.2 (level a w).val (Nat.le_of_lt_succ (level a w).isLt)‖ ≤
          ε * ‖g (r a) ^ N‖ := by
  apply (MSOPEPhysicalTransfer.remainder_isLittleO_iff F Q J hJ hQ U v
    M η hM hη g hg hG r hr x hx p Z B N).trans
  apply SignedTensor.littleO_iff_frequent_regulator
  · filter_upwards [hx, hr.eventually
      (WilsonWholeLimit.detector_separated_in_room (I := Fin n) U M η hη)] with a hxa hsep
    exact candidate_tendsto F hS J U p Z (B a) v N (g (r a)) (r a) (x a)
      (hsep _ hxa) (level a)
  · exact (hr.eventually hg.positive).mono fun _ ha => pow_ne_zero N ha.ne'

/-- One threshold covers all independent fields at this detector, horizon and
order. The only signed estimates assumed are on the finitely many basis tuples,
each on its own cofinal set in the original mesh-before-period schedule. -/
theorem uniform_remainder_iff_frequent_basis (F : Final C f S) (hS : Services C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hQ : Foundation F Q)
    (U : Detector S D) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
    (g : ℝ → ℝ) (hg : Trace.Pilot.Coupling G g) (hG : G.Simple)
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → Fin n → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : A → Blocks C.labels n i D) (N : ℕ)
    (level : sheaf C.labels n i → (a : A) → (w : ℕ × ℕ) → Fin (w.1 + 1)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ v : Fin n → E C.labels i,
      ‖actualOutput F Q J v (r a) (x a) - composedTruncation p Z (B a) v N (g (r a))‖ ≤
        ε * ‖g (r a) ^ N‖ * ∏ j, ‖v j‖) ↔
    ∀ u : sheaf C.labels n i, ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l,
      ∃ᶠ w : ℕ × ℕ in f.fuse,
        let v := fun j => (RG11.Fields.tower C.labels i).b (u j)
        ‖finiteReadout J U v (r a) (x a)
          (candidate J p Z (B a) v N (g (r a)) (r a))
          w.1 w.2 (level u a w).val (Nat.le_of_lt_succ (level u a w).isLt)‖ ≤
            ε * ‖g (r a) ^ N‖ := by
  let T a := actualTensor (i := i) (D := D) F Q J (r a) (x a) -
    formalTensor p Z (B a) N (g (r a))
  have app a (v : Fin n → E C.labels i) : T a v =
      actualOutput F Q J v (r a) (x a) - composedTruncation p Z (B a) v N (g (r a)) := by
    rw [show T a v = actualTensor F Q J (r a) (x a) v -
      formalTensor p Z (B a) N (g (r a)) v from rfl, actualTensor_apply, formalTensor_apply]
  have h := SignedTensor.uniform_iff_basis_littleO (l := l)
    (RG11.Fields.tower C.labels i).b T (fun a => g (r a) ^ N)
  simp only [app] at h
  refine h.trans (forall_congr' (fun u => ?_))
  exact remainder_iff_frequent_bound F hS Q J hJ hQ U _ M η hM hη g hg hG
    r hr x hx p Z B N (level u)

end YM.Integration.SignedUniformReadout
