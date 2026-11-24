import YM.Integration.ActualOriginalQPackets
import YM.Integration.ActualOriginalQPointDatum
import YM.Corona.Halo

/-!
# Uniform cover of the complete original-Q point packet

The fixed union contains the degree-zero reader stencil and every original
Glyph section stencil. Its coordinate radius bounds the full token plots,
with their connected-cover convention, at every positive BudgetPoint block.
No path-length or cardinality-only substitute is used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQPointCover
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open Comparison.Density.RenderM
open ActualOriginalQReaders ActualOriginalQPackets
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {V : Type} [Fintype V] (u : V → MS.Rake.Label B)

def stencil : Finset Cover :=
  (R.family.localSection 0).stencil ∪
    Finset.univ.biUnion (fun s : Slot u =>
      (R.family.localSection s.2.size).stencil)

def radius : ℕ :=
  (stencil R u).sup fun z => Finset.univ.sup fun i => (z i).natAbs

def bound : ℕ := (radius R u + radius R u + 1) ^ 4

private theorem stencil_halo {n : Side} (o : Site n) (P : BudgetPoint) :
    (stencil R u).image (fun z => wrap n z + o) ⊆
      halo (radius R u * P.B) {o} := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  apply halo_spec.mpr
  refine ⟨o, Finset.mem_singleton_self _, ?_⟩
  rw [separation_comm, separation, add_sub_cancel_right]
  apply Finset.sup_le
  intro i _
  have hzi : (z i).natAbs ≤ radius R u :=
    (Finset.le_sup (f := fun j => (z j).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun v : Cover =>
        Finset.univ.sup fun j => (v j).natAbs) hz)
  exact (Corona.lap z i).trans
    (hzi.trans (Nat.le_mul_of_pos_right _ P.B_pos))

variable (p L : ℕ)
    (o : V → Site (R.family.side L p)) (order weight : V → ℕ)

local notation "D₀" => ActualOriginalQPointDatum.datum R p L o order weight

private theorem plot_subset (i : V) :
    plot D₀ u i ⊆
      (stencil R u).image (fun z => wrap (R.family.side L p) z + o i) := by
  change
    (R.family.localSection 0).footprint (ActualRunQlocalNativeTuple.root D₀ i) ∪
      (Finset.univ : Finset (MS.Menus.Glyph B (u i).h)).biUnion
        (fun g => (R.family.localSection g.size).footprint
          (ActualRunQlocalNativeTuple.root D₀ i)) ⊆ _
  simp only [ActualOriginalQPointDatum.root_eq]
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_union_left _ hz, rfl⟩
  · obtain ⟨g, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨z, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨⟨i, g⟩, Finset.mem_univ _, hz⟩), rfl⟩

/-- One fixed connected-cover bound for every full original point-Q plot. -/
theorem plot_cover (P : BudgetPoint) (i : V) :
    coverNumber P.B (plot D₀ u i) ≤ bound R u := by
  exact (Corona.cover_mono
    ((plot_subset R u p L o order weight i).trans
      (stencil_halo R u (o i) P)) P.B).trans
        (Corona.tile (o i) (radius R u) P.B P.B_pos)

variable [DecidableEq V] (Q : MS.Land.Prescription B) (μ : ℝ) (orders : V → ℕ)

private theorem token_cover (N : ℕ) (P : BudgetPoint) (i : ℕ)
    (T : Token G (R.family.side L p)
      (fun j => (ActualRunQlocalNativeTuple.orbit D₀ j).Mood)
      ((packets Q D₀ u μ orders N).rank i))
    (hT : (packets Q D₀ u μ orders N).packet i = some T) :
    coverNumber P.B T.plot ≤ bound R u := by
  unfold packets at hT ⊢
  exact MarkedPackets.ofFin_all _ _ _ _ _ _
    (fun _ _ _ T => coverNumber P.B T.plot ≤ bound R u)
    (fun _ => plot_cover R u p L o order weight P _) i T hT

/-- The literal finite packetCover, with arbitrary requested BudgetPoint.
The constant is fixed before all cutoffs, periods, roots, tests and fees. -/
theorem packet_cover (N : ℕ) (P : BudgetPoint) :
    packetCover Q D₀ u μ orders N P ≤ bound R u := by
  unfold packetCover NativeFinitePacketPayment.coverOffset
  apply Finset.sup_le
  intro i _
  cases hT : (packets Q D₀ u μ orders N).packet i with
  | none =>
    simp only [NativeFinitePacketPayment.coverAt, hT]
    exact Nat.zero_le _
  | some T =>
    simpa only [NativeFinitePacketPayment.coverAt, hT] using
      token_cover R u p L o order weight Q μ orders N P i T hT

end YM.Integration.ActualOriginalQPointCover
end
