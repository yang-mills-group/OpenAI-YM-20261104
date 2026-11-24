import YM.Integration.WilsonOffsetReportingProducts

/-! The true two stencils attached to each displaced insertion eventually
avoid every other equation radius at fixed positive physical clearance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOffsetSites
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetReportingProducts
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}

theorem footprint (V : SectionData (C.labels.level d)) :
    ∃ L : ℕ, ∀ᶠ N : ℕ in atTop, ∀ p (o : Site (C.side N p)) y,
       y ∈ V.footprint o → separation y o ≤ L := by
  let s := V.stencil
  choose r M hr using fun i : s => Mark.place_size i.val
  refine ⟨Finset.univ.sup r,?_⟩
  filter_upwards [Mark.lengths C.S (Finset.univ.sup M)] with N hn
  intro p o y hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
  let j : s := ⟨i,hi⟩
  rw [separation,add_sub_cancel_right]
  exact ((hr j _ ((Finset.le_sup (f:=M) (Finset.mem_univ j)).trans (hn p))).2).trans
    (Finset.le_sup (f:=r) (Finset.mem_univ j))

theorem avoids {I : Type} [Fintype I] (V : ∀ d, SectionData (C.labels.level d))
    (radius : ℕ → ℕ) (d : I → ℕ) (δ : ℝ) (positive : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ p (o : I → Site (C.side N p)),
      (∀ i j, i ≠ j → δ ≤ C.S.a N * separation (o i) (o j)) → Avoids V radius d o := by
  choose lv vc using fun i:I => footprint (V (d i))
  choose lf fc using fun i:I => footprint (C.localSection (d i))
  let wall := Finset.univ.sup (fun i:I => radius (d i)) + (Finset.univ.sup lv ⊔ Finset.univ.sup lf)
  have small : ∀ᶠ N : ℕ in atTop, C.S.a N * wall < δ := by
    have limit := C.S.shrinks.mul_const (wall:ℝ)
    rw [zero_mul] at limit
    exact limit.eventually (gt_mem_nhds positive)
  filter_upwards [small,eventually_all.mpr vc,eventually_all.mpr fc] with N room hV hF
  intro p o far i j ij
  have apart : wall < separation (o j) (o i) := by
    exact_mod_cast (lt_of_mul_lt_mul_left (room.trans_le (far j i (Ne.symm ij))) (C.S.a_pos N).le)
  have Hr : radius (d i) ≤ Finset.univ.sup (fun i:I => radius (d i)) :=
    Finset.le_sup (f:=fun i:I => radius (d i)) (Finset.mem_univ i)
  have L₁ : lf j ≤ Finset.univ.sup lv ⊔ Finset.univ.sup lf :=
    (Finset.le_sup (f:=lf) (Finset.mem_univ j)).trans le_sup_right
  have L₂ : lv j ≤ Finset.univ.sup lv ⊔ Finset.univ.sup lf :=
    (Finset.le_sup (f:=lv) (Finset.mem_univ j)).trans le_sup_left
  constructor
  · intro y hy
    have hy' := hF j p (o j) y hy
    have tri := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at tri
    change radius (d i) < separation y (o i)
    unfold wall at apart
    omega
  · intro y hy
    have hy' := hV j p (o j) y hy
    have tri := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at tri
    change radius (d i) < separation y (o i)
    unfold wall at apart
    omega

end YM.Integration.WilsonSeparatedOffsetSites
