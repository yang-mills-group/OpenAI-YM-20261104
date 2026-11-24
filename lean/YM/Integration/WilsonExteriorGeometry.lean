import YM.Integration.WilsonWholeLimit
import YM.OPE.Cards.Scale

/-! Literal ceiling placements in common shifted cells.  The same cells work
under every coarse-grid translation, so the margin budget does not depend on
the number of replicas.  Disjointness and the central signed price are separate
obligations; no estimate for either is asserted here. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonExteriorGeometry

open Function Filter Set Lattice Cells Extraction OPE OPE.Orbits
open Next.Phase StressFlux.Matching
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {N p b : ℕ}

/-- Right-ceiling rounding commutes exactly with an original coarse-grid
translation, including positions on a rounding boundary. -/
lemma ceilSite_add_grid (h : b ≤ N) (x : E4) (z : Cover) :
    ceilSite C N p (x + C.S.gridPoint b z) =
      ceilSite C N p x + location C.S b N p z := by
  rw [location, dif_pos h, Ratio.embed_wrap]
  unfold ceilSite
  rw [← map_add]
  apply congrArg (wrap (C.side N p))
  funext a
  simp only [Pi.add_apply, nsmul_eq_mul]
  change ⌈(x a + C.S.a b * (z a : ℝ)) / C.S.a N⌉ =
    ⌈x a / C.S.a N⌉ + (span C.S h p : ℤ) * z a
  have hscale : C.S.a N * (span C.S h p : ℝ) = C.S.a b :=
    C.S.embeds_scale (C.S.toDepth h p)
  have hq : (x a + C.S.a b * (z a : ℝ)) / C.S.a N =
      x a / C.S.a N + (((span C.S h p : ℤ) * z a : ℤ) : ℝ) := by
    rw [← hscale]
    push_cast
    field_simp [(C.S.a_pos N).ne']
  rw [hq, Int.ceil_add_intCast]

/-- This is the literal product of the original C.seen representatives, with
the same shift on its finite Wilson configuration. -/
lemma product_add_grid {S : Table C.book} {I : Type} [Fintype I] {d : I → ℕ}
    (h : b ≤ N) (x : I → E4) (v : Labels S d) (z : Cover) :
    WilsonWholeLimit.product (fun i => x i + C.S.gridPoint b z) v N p =
      WilsonWholeLimit.product x v N p ∘ translate (location C.S b N p z) := by
  funext U
  unfold WilsonWholeLimit.product
  dsimp only [comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [ceilSite_add_grid h]
  exact (C.translation _ _ (names v i).2 U).symm

/-- A common coarse-grid shift preserves the actual ceiling site's margin in
any compatible link tiling. -/
lemma inside_ceilSite_add_grid (h : b ≤ N)
    (T : Tiling (C.side N p)) (hT : T.kind = .link)
    (hd : T.side.val ∣ span C.S h p) {q : ℕ} {x : E4}
    (hx : Inside T q (ceilSite C N p x)) (z : Cover) :
    Inside T q (ceilSite C N p (x + C.S.gridPoint b z)) := by
  rw [ceilSite_add_grid h, location, dif_pos h, Ratio.embed_wrap]
  rw [inside_stripe T hT] at hx ⊢
  intro a
  rw [Cards.sameResidue T z _ hd]
  exact hx a

/-- Fit one copy of the actual central and exterior sites.  The same two
shifted tilings then fit every coarse-grid translate of that copy. -/
theorem seats_for_all_grid_translates {I J : Type} [Fintype I] [Fintype J]
    {f l n : ℕ} (hbf : b ≤ f) (hfl : f ≤ l) (hln : l ≤ n) (hn : n ≤ N)
    (x : I → E4) (y : J → E4)
    (hI : (Fintype.card I : ℝ) * (2 * (5 * C.S.a f)) < C.S.a b)
    (hJ : (Fintype.card J : ℝ) * (2 * (3 * C.S.a n)) < C.S.a l) :
    ∃ o : Site (C.side N p),
      let T := (center C.S p (hbf.trans (hfl.trans (hln.trans hn))) 0).newly o
      let W := (center C.S p (hln.trans hn) 0).newly o
      ∀ z : Cover,
        (∀ i, Inside T (3 * span C.S (hfl.trans (hln.trans hn)) p)
          (ceilSite C N p (x i + C.S.gridPoint b z))) ∧
        (∀ i, Inside W (3 * span C.S hn p)
          (ceilSite C N p (y i + C.S.gridPoint b z))) := by
  obtain ⟨o, ho, hw⟩ := Cards.seats C (hfl.trans (hln.trans hn)) hbf hfl hln hn
    (fun i => ceilSite C N p (x i)) (fun i => ceilSite C N p (y i)) hI hJ
  refine ⟨o, fun z => ⟨?_, ?_⟩⟩
  · intro i
    exact inside_ceilSite_add_grid (hbf.trans (hfl.trans (hln.trans hn)))
      _ rfl (dvd_refl _) (ho i) z
  · intro i
    exact inside_ceilSite_add_grid (hbf.trans (hfl.trans (hln.trans hn)))
      _ rfl (Around.inherits (C := C) (hbf.trans hfl) (hln.trans hn)) (hw i) z

private lemma buffer_scale (S : Schedule) (P b m : ℕ) (c : ℝ) :
    ∃ f : ℕ, max b m ≤ f ∧ (P : ℝ) * (2 * (c * S.a f)) < S.a b := by
  have ht : Tendsto (fun f => (P : ℝ) * (2 * (c * S.a f))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((S.shrinks.const_mul c).const_mul 2).const_mul (P : ℝ)
  exact ((eventually_ge_atTop (max b m)).and
    (ht.eventually (gt_mem_nhds (S.a_pos b)))).exists

/-- The numeric margin budget can itself be chosen before the fine cutoff,
period, physical positions, and any replica set.  This includes a single
central complete discrepancy by taking I = Unit. -/
theorem literal_replicas_have_seats {I J : Type} [Fintype I] [Fintype J]
    (b centralMin exteriorMin : ℕ) :
    ∃ f : ℕ, max b centralMin ≤ f ∧
    ∃ n : ℕ, max f exteriorMin ≤ n ∧
      ∀ N : ℕ, ∀ hn : n ≤ N, ∀ p : ℕ, ∀ x : I → E4, ∀ y : J → E4,
      ∃ hbf : b ≤ f, ∃ hfn : f ≤ n, ∃ o : Site (C.side N p),
        let T := (center C.S p (hbf.trans (hfn.trans hn)) 0).newly o
        let W := (center C.S p (hfn.trans hn) 0).newly o
        ∀ z : Cover,
          (∀ i, Inside T (3 * span C.S (hfn.trans hn) p)
            (ceilSite C N p (x i + C.S.gridPoint b z))) ∧
          (∀ i, Inside W (3 * span C.S hn p)
            (ceilSite C N p (y i + C.S.gridPoint b z))) := by
  obtain ⟨f, hf, hI⟩ := buffer_scale C.S (Fintype.card I) b centralMin 5
  obtain ⟨n, hn, hJ⟩ := buffer_scale C.S (Fintype.card J) f exteriorMin 3
  have hbf : b ≤ f := (le_max_left _ _).trans hf
  have hfn : f ≤ n := (le_max_left _ _).trans hn
  refine ⟨f, hf, n, hn, fun N hN p x y => ⟨hbf, hfn, ?_⟩⟩
  exact seats_for_all_grid_translates hbf le_rfl hfn hN x y hI hJ

end YM.Integration.WilsonExteriorGeometry
