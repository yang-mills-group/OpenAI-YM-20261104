import YM.Integration.ActualFoundryDetectorMean
import YM.Integration.WilsonMixedPlacement
import YM.Spec.Closed

/-! The complete signed detector has separate central and exterior cells.
The exterior prices below are supplied by the retained construction before
bounded labels are chosen. Only the sharp central discrepancy price remains
an input; a rough joint polynomial bound is not substituted for it. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualFoundryDetectorSource
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Cells Extraction
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open NativeSignedBranches StressFlux.Matching OPE.Therm OPE.Cards
open WilsonMixedPlacement WilsonExteriorTrains
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {E : Type} [Fintype E] [DecidableEq E]
    {arity : ℕ}

def central (N p : ℕ) (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (x : Fin (arity + 1) → E4) :
    Config G (C.side N p) → ℂ := fun U =>
  (∏ j, C.O N p (v j).2 (ceilSite C N p (x j)) U) -
    C.O N p z.2 (ceilSite C N p 0) U

omit [DecidableEq E] in
/-- One exterior coefficient bank works for every independent bounded
choice of the physical labels. Its constants precede the exterior level. -/
theorem exterior_bounds {f : Extraction.Order} {S : Table C.book}
    (F : Spec.Final C f S) (d : E → ℕ) (R : E → ℝ) (hR : ∀ i, 0 < R i)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ η : ℝ, 0 < η →
        ∀ᶠ w : ℕ × ℕ in f.fuse,
          ∀ e : (i : E) → C.label (d i), (∀ i, ‖e i‖ ≤ R i) → ∀ i,
            PaidAt C.S w.1 w.2 n (C.beta w.1 w.2)
              (A i * C.S.a n ^ (-(d i : ℝ) - δ) + η)
              (C.O w.1 w.2 (e i) 0) := by
  choose t ht A hA h using fun i => F.room.copies.centered (d i) δ (R i) hδ (hR i)
  refine ⟨univ.sup t, A, hA, fun n hn η hη => ?_⟩
  have hp (i : E) : ∀ᶠ w : ℕ × ℕ in f.fuse,
      ∃ hN : n ≤ w.1, ∀ e : C.label (d i), ‖e‖ ≤ R i →
        ∀ x : Site (C.side w.1 w.2),
          Interior ((center C.S w.2 hN x).chamber 0) (C.O w.1 w.2 e x) ∧
          (center C.S w.2 hN x).rootTest (C.beta w.1 w.2) (C.O w.1 w.2 e x) ≤
            A i * C.S.a n ^ (-(d i : ℝ) - δ) + η :=
    (Order.fused f _).mpr (h i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) η hη)
  filter_upwards [eventually_all.mpr hp] with w hw
  intro e he i
  obtain ⟨hN, hi⟩ := hw i
  exact ⟨hN, (hi (e i) (he i) 0).1, (hi (e i) (he i) 0).2⟩

omit [DecidableEq E] in
/-- The mixed-cell supplier acts on the literal whole physical detector.
The central cell may shrink through Q while the exterior level n stays fixed. -/
theorem mixed_bound (hC : C.Makes) {b q n Q t N p : ℕ}
    {hbq : b ≤ q} {hqn : q ≤ n} (y : E → E4)
    (P : PlacementAt C b q n hbq hqn (fun _ : Unit => 0) y 1 t N p)
    (hqQ : q ≤ Q) (hQ : Q ≤ N)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (x : Fin (arity + 1) → E4) (a : ℝ) (B : E → ℝ)
    (hcentral : PaidAt C.S N p Q (C.beta N p) a (central N p v z x))
    (hexterior : ∀ i, PaidAt C.S N p n (C.beta N p) (B i) (C.O N p (e i).2 0)) :
    ‖moment (C.beta N p) (physical C N p v z e x y)‖ ≤ a * ∏ i, B i := by
  have hp := P.price hC hqQ hQ (fun _ : Unit => a) B
    (fun _ => central N p v z x) (fun j => C.O N p (e j.2).2 0)
    (fun _ => hcentral) (fun j => hexterior j.2)
  have ht (w : E4) : train C b t 0 w = w := by
    apply PiLp.ext
    intro i
    simp [train, Schedule.gridPoint, Work.B15.diag]
  have hz : ceilSite C N p (0 : E4) = 0 := by
    simp [ceilSite, show (fun _ : Axis => (0 : ℤ)) = (0 : Cover) from rfl]
  have hzero (U : Config G (C.side N p)) : translate (0 : Site (C.side N p)) U = U := by
    funext a
    simp [Lattice.translate]
  have hf : (fun U =>
      (∏ i : Fin 1 × Unit, central N p v z x
        (translate (ceilSite C N p (train C b t i.1 (0 : E4))) U)) *
      ∏ j : Fin 1 × E, C.O N p (e j.2).2 0
        (translate (ceilSite C N p (train C b t j.1 (y j.2))) U)) =
      physical C N p v z e x y := by
    funext U
    simp only [Fintype.prod_prod_type, Fintype.prod_unique]
    change central N p v z x
        (translate (ceilSite C N p (train C b t 0 (0 : E4))) U) *
        (∏ i : E, C.O N p (e i).2 0
          (translate (ceilSite C N p (train C b t 0 (y i))) U)) =
      central N p v z x U * ∏ i : E, C.O N p (e i).2 (ceilSite C N p (y i)) U
    have hc : central N p v z x
        (translate (ceilSite C N p (train C b t 0 (0 : E4))) U) =
        central N p v z x U := by rw [ht, hz, hzero]
    rw [hc]
    apply congrArg (fun w : ℂ => central N p v z x U * w)
    apply Finset.prod_congr rfl
    intro i _
    rw [ht]
    simpa only [zero_add] using C.translation 0 (ceilSite C N p (y i)) (e i).2 U
  rw [hf] at hp
  simpa only [Fintype.prod_unique, pow_one] using hp

/-- Exact normalization followed by the concrete multi-cell readout.
The original whole numerator is retained at every intermediate level m. -/
theorem normalized_mixed_bound (hC : C.Makes) {b q n Q t N p m : ℕ}
    {hbq : b ≤ q} {hqn : q ≤ n} (y : E → E4)
    (P : PlacementAt C b q n hbq hqn (fun _ : Unit => 0) y 1 t N p)
    (hqQ : q ≤ Q) (hQ : Q ≤ N) (hm : m ≤ N)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (unitDegree zeroDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (x : Fin (arity + 1) → E4) (a : ℝ) (B : E → ℝ)
    (hcentral : PaidAt C.S N p Q (C.beta N p) a (central N p v z x))
    (hexterior : ∀ i, PaidAt C.S N p n (C.beta N p) (B i) (C.O N p (e i).2 0)) :
    ‖∫ U, (actualSignedTransport C (N := N)
        (numerator C N p v z e unitDegree zeroDegree x y) hm U).part
        (Stock.final (Region E)) ∂scene C.path N p m‖ ≤ a * ∏ i, B i := by
  rw [normalized_mean C hC N p v z e unitDegree zeroDegree hUnit x y hm]
  exact mixed_bound hC y P hqQ hQ v z e x a B hcentral hexterior

/-- The retained construction supplies every exterior price and the native
mixed-cell geometry. Only the signed central PaidAt estimate is supplied by
the sharp local comparison. Geometry and exterior constants are chosen before
the bounded exterior labels, the central test data, and the readout depth. -/
theorem complete_readout {f : Extraction.Order} {S : Table C.book}
    (F : Spec.Final C f S) (d : E → ℕ) (R : E → ℝ) (hR : ∀ i, 0 < R i)
    (δ : ℝ) (hδ : 0 < δ) (y : E → E4)
    (hy : Injective (Sum.elim (fun _ : Unit => (0 : E4)) y))
    (minB bufferMin : ℕ) :
    ∃ b : ℕ, minB ≤ b ∧ ∃ q : ℕ, max b bufferMin ≤ q ∧
      ∃ n : ℕ, q ≤ n ∧ ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
        ∀ᶠ w : ℕ × ℕ in f.fuse,
          ∀ Q : ℕ, q ≤ Q → Q ≤ w.1 →
          ∀ e : (i : E) → C.label (d i), (∀ i, ‖e i‖ ≤ R i) →
          ∀ (v : Fin (arity + 1) → (a : ℕ) × C.label a)
            (z : (a : ℕ) × C.label a) (x : Fin (arity + 1) → E4) (a : ℝ),
          PaidAt C.S w.1 w.2 Q (C.beta w.1 w.2) a (central w.1 w.2 v z x) →
          ∀ unitDegree zeroDegree : ℕ, C.ref unitDegree ≤ w.1 →
          ∀ m : ℕ, ∀ hm : m ≤ w.1,
            ‖∫ U, (actualSignedTransport C (N := w.1)
                (numerator C w.1 w.2 v z (fun i => ⟨d i, e i⟩)
                  unitDegree zeroDegree x y) hm U).part
                (Stock.final (Region E)) ∂scene C.path w.1 w.2 m‖ ≤
              a * ∏ i, (A i * C.S.a n ^ (-(d i : ℝ) - δ) + 1) := by
  obtain ⟨n₀, A, hA, hpaid⟩ := exterior_bounds F d R hR δ hδ
  obtain ⟨b, hb, q, hq, n, hn, hbq, hqn, hplaces⟩ :=
    placements f (fun _ : Unit => (0 : E4)) y hy minB bufferMin n₀
  refine ⟨b, hb, q, hq, n, hqn, A, hA, ?_⟩
  obtain ⟨t, ht⟩ := (hplaces 1).exists
  filter_upwards [ht, hpaid n ((le_max_right q n₀).trans hn) 1 one_pos]
    with w hw he
  obtain ⟨P⟩ := hw
  intro Q hqQ hQ e hE v z x a ha unitDegree zeroDegree hUnit m hm
  exact normalized_mixed_bound F.room.cutoff y P hqQ hQ hm v z
    (fun i => ⟨d i, e i⟩) unitDegree zeroDegree hUnit x a
    (fun i => A i * C.S.a n ^ (-(d i : ℝ) - δ) + 1) ha (he e hE)

end YM.Integration.ActualFoundryDetectorSource
