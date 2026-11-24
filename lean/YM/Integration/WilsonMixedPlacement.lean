import YM.Integration.WilsonExteriorTrains

/-! Two actual link tilings for the complete central cylinders and separate
exterior cylinders.  All levels are chosen before the replica count. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonMixedPlacement

open Function Filter Set Lattice Cells Extraction StressFlux.Matching OPE
open Next.Phase WilsonExteriorTrains WilsonExteriorSeparation
open scoped Topology Classical BigOperators

variable {G : Gauge} {C : Family G} {I J : Type} [Fintype I] [Fintype J]

structure PlacementAt (C : Family G) (b q n : ℕ) (hbq : b ≤ q) (hqn : q ≤ n)
    (x : I → E4) (y : J → E4) (m t N p : ℕ) where
  live : n ≤ N
  offset : Site (C.side N p)
  central (i : Fin m × I) :
    Inside ((center C.S p (hbq.trans (hqn.trans live)) 0).newly offset)
      (3 * span C.S (hqn.trans live) p)
      (ceilSite C N p (train C b t i.1 (x i.2)))
  exterior (j : Fin m × J) :
    Inside ((center C.S p (hqn.trans live) 0).newly offset)
      (3 * span C.S live p) (ceilSite C N p (train C b t j.1 (y j.2)))
  central_apart (i j : Fin m × I) (h : i ≠ j) :
    span C.S (hbq.trans (hqn.trans live)) p <
      separation (ceilSite C N p (train C b t i.1 (x i.2)))
        (ceilSite C N p (train C b t j.1 (x j.2)))
  exterior_apart (i j : Fin m × J) (h : i ≠ j) :
    span C.S (hqn.trans live) p <
      separation (ceilSite C N p (train C b t i.1 (y i.2)))
        (ceilSite C N p (train C b t j.1 (y j.2)))
  between (i : Fin m × I) (j : Fin m × J) :
    span C.S (hbq.trans (hqn.trans live)) p <
      separation (ceilSite C N p (train C b t i.1 (x i.2)))
        (ceilSite C N p (train C b t j.1 (y j.2)))

/-- Arbitrary separated physical centers acquire actual mixed-cell placement.
Only the train and cutoff tails, not the selected levels, depend on m. -/
theorem placements (f : Extraction.Order) (x : I → E4) (y : J → E4)
    (hxy : Injective (Sum.elim x y)) (minB bufferMin exteriorMin : ℕ) :
    ∃ b : ℕ, minB ≤ b ∧ ∃ q : ℕ, max b bufferMin ≤ q ∧
      ∃ n : ℕ, max q exteriorMin ≤ n ∧
      ∃ hbq : b ≤ q, ∃ hqn : q ≤ n, ∀ m : ℕ,
        ∀ᶠ t : ℕ in atTop, ∀ᶠ z : ℕ × ℕ in f.fuse,
          Nonempty (PlacementAt C b q n hbq hqn x y m t z.1 z.2) := by
  obtain ⟨b, hb, hgap⟩ := ((eventually_ge_atTop minB).and
    (eventual_coordinate_gaps C (Sum.elim x y) hxy)).exists
  obtain ⟨q, hq, n, hn, hseats⟩ :=
    WilsonExteriorGeometry.literal_replicas_have_seats (C := C) (I := I) (J := J)
      b bufferMin exteriorMin
  have hbq : b ≤ q := (le_max_left _ _).trans hq
  have hqn : q ≤ n := (le_max_left _ _).trans hn
  refine ⟨b, hb, q, hq, n, hn, hbq, hqn, fun m => ?_⟩
  have hN : ∀ᶠ z : ℕ × ℕ in f.fuse, n ≤ z.1 := by
    rw [Order.fused, Order.late]
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop n
  filter_upwards [literal_trains_apart C (f := f) b m (Sum.elim x y) hgap]
    with t ht
  filter_upwards [ht, hN] with z hz hN
  obtain ⟨_, _, o, ho⟩ := hseats z.1 hN z.2 x y
  have hsmall : span C.S (hqn.trans hN) z.2 ≤
      span C.S (hbq.trans (hqn.trans hN)) z.2 :=
    Nat.le_of_dvd (C.S.toDepth (hbq.trans (hqn.trans hN)) z.2).count.property
      (Around.inherits (C := C) hbq (hqn.trans hN))
  refine ⟨{
    live := hN
    offset := o
    central := fun i => (ho (Work.B15.diag t i.1)).1 i.2
    exterior := fun j => (ho (Work.B15.diag t j.1)).2 j.2
    central_apart := ?_
    exterior_apart := ?_
    between := ?_ }⟩
  · intro i j hij
    exact hz (hbq.trans (hqn.trans hN)) (i.1, Sum.inl i.2) (j.1, Sum.inl j.2)
      (by
        intro h
        have hfirst : i.1 = j.1 := congrArg (fun z : Fin m × Sum I J => z.1) h
        have hsecond : (Sum.inl i.2 : Sum I J) = Sum.inl j.2 :=
          congrArg (fun z : Fin m × Sum I J => z.2) h
        exact hij (Prod.ext hfirst (Sum.inl.inj hsecond)))
  · intro i j hij
    exact hsmall.trans_lt (hz (hbq.trans (hqn.trans hN))
      (i.1, Sum.inr i.2) (j.1, Sum.inr j.2)
      (by
        intro h
        have hfirst : i.1 = j.1 := congrArg (fun z : Fin m × Sum I J => z.1) h
        have hsecond : (Sum.inr i.2 : Sum I J) = Sum.inr j.2 :=
          congrArg (fun z : Fin m × Sum I J => z.2) h
        exact hij (Prod.ext hfirst (Sum.inr.inj hsecond))))
  · intro i j
    exact hz (hbq.trans (hqn.trans hN)) (i.1, Sum.inl i.2) (j.1, Sum.inr j.2)
      (by
        intro h
        have hsecond : (Sum.inl i.2 : Sum I J) = Sum.inr j.2 :=
          congrArg (fun z : Fin m × Sum I J => z.2) h
        cases hsecond)

/-- Apply the native mixed chessboard supplier to these actual placements.
The central and exterior PaidAt receipts remain separate and unchanged.
The central root may be at any finer Q; exterior prices do not follow Q. -/
theorem PlacementAt.price {b q n Q m t N p : ℕ} {hbq : b ≤ q} {hqn : q ≤ n}
    {x : I → E4} {y : J → E4}
    (P : PlacementAt C b q n hbq hqn x y m t N p) (hC : C.Makes)
    (hqQ : q ≤ Q) (hQ : Q ≤ N)
    (A : I → ℝ) (B : J → ℝ)
    (F : Fin m × I → Wilson.Config G (C.side N p) → ℂ)
    (Z : Fin m × J → Wilson.Config G (C.side N p) → ℂ)
    (hF : ∀ i, Cards.PaidAt C.S N p Q (C.beta N p) (A i.2) (F i))
    (hZ : ∀ j, Cards.PaidAt C.S N p n (C.beta N p) (B j.2) (Z j)) :
    ‖Wilson.moment (C.beta N p) (fun U =>
      (∏ i : Fin m × I, F i (translate
        (ceilSite C N p (train C b t i.1 (x i.2))) U)) *
      ∏ j : Fin m × J, Z j (translate
        (ceilSite C N p (train C b t j.1 (y j.2))) U))‖ ≤
      ((∏ i, A i) * ∏ j, B j)^m := by
  let T := (center C.S p (hbq.trans (hqn.trans P.live)) 0).newly P.offset
  let W := (center C.S p (hqn.trans P.live) 0).newly P.offset
  have hW : W.side.val ∣ T.side.val :=
    Around.inherits (C := C) hbq (hqn.trans P.live)
  have hsmall : span C.S hQ p ≤ span C.S (hqn.trans P.live) p :=
    Nat.le_of_dvd (C.S.toDepth (hqn.trans P.live) p).count.property
      (Around.inherits (C := C) hqQ hQ)
  have hcentral (i : Fin m × I) : Inside T (3 * span C.S hQ p)
      (ceilSite C N p (train C b t i.1 (x i.2))) :=
    Extraction.Lease.fewer T _ (Nat.mul_le_mul_left 3 hsmall) (P.central i)
  have h := Cards.plant (W₀ := W) (W := T) rfl rfl rfl hW
    P.live (Around.inherits (C := C) hqn P.live)
    hQ (Around.inherits (C := C) (hbq.trans hqQ) hQ)
    (fun j : Fin m × J => ceilSite C N p (train C b t j.1 (y j.2))) Z (fun j => B j.2)
    (fun i : Fin m × I => ceilSite C N p (train C b t i.1 (x i.2))) F (fun i => A i.2)
    P.exterior P.exterior_apart hcentral P.central_apart P.between hZ hF
    (Cells.seamless hC N p)
  simpa only [comp_apply, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow] using h

end YM.Integration.WilsonMixedPlacement
