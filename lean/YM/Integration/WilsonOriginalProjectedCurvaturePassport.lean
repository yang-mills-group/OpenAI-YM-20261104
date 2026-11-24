import YM.Integration.WilsonOriginalProjectedCurvatureRoster

/-! A single lifted walk covers the complete original test stub and every allowed
curvature-glyph footprint. Its length is fixed by those lifted stencils before
choosing a period, and passage to the torus uses their actual occupied images. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvaturePassport
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Earn
open QuadraticLocal.Earn.Cable
open PhysicalNext.Repeat.Legato LocalComparison Push Push.AbsoluteSums
open scoped Classical BigOperators

private def outward (y : Cover) : Walk := route 0 y 1

private theorem reaches {c : Side} (x : Site c) (y : Cover) :
    stop x (outward y) = x + wrap c y := by
  unfold outward
  nth_rw 1 [show x = x + wrap c 0 from by simp]
  rw [Work.E03.stop_add_left, ← wrap_stop_cover, route_end]

private def roundTrips : List Cover → Walk
  | [] => []
  | y :: ys => (outward y ++ Lattice.reverse (outward y)) ++ roundTrips ys

private theorem covers {c : Side} (x : Site c) {ys : List Cover} {y : Cover}
    (h : y ∈ ys) : x + wrap c y ∈ Paths.native x (roundTrips ys) := by
  induction ys with
  | nil => simp at h
  | cons z zs ih =>
    rw [roundTrips, Native.combine, Native.combine, stop_append, reverse_stop]
    rcases List.mem_cons.mp h with e|e
    · subst z
      exact mem_union_left _ (mem_union_left _ (reaches x y ▸ Native.tip x (outward y)))
    · exact mem_union_right _ (ih e)

private theorem length (ys : List Cover) : (roundTrips ys).length =
    2 * (ys.map (fun y => (outward y).length)).sum := by
  induction ys with
  | nil => rfl
  | cons z zs ih =>
    simp only [roundTrips, List.length_append, Lattice.reverse, List.length_map,
      List.length_reverse, ih, List.map_cons, List.sum_cons]
    omega

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type}
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V) (u : V → MS.Rake.Label B)

def stencil (i : V) : Finset Cover :=
  (R.family.localSection (ActualRunQlocalNativeTuple.grade D i)).stencil ∪
    (Finset.univ : Finset (MS.Menus.Glyph B (u i).h)).biUnion
      (fun g => (R.family.localSection g.size).stencil)

theorem plot (i : V) : ActualOriginalQPackets.plot D u i =
    (stencil D u i).image (fun y => wrap (R.family.side L p) y +
      ActualRunQlocalNativeTuple.root D i) := by
  unfold ActualOriginalQPackets.plot stencil
  rw [Finset.image_union]
  congr 1
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, SectionData.footprint, Finset.mem_image]
  constructor
  · rintro ⟨g,y,hy,rfl⟩
    exact ⟨y,⟨g,hy⟩,rfl⟩
  · rintro ⟨y,⟨g,hy⟩,rfl⟩
    exact ⟨g,y,hy,rfl⟩

def paper : Passport (R.family.side L p) V where
  origin := ActualRunQlocalNativeTuple.root D
  support := ActualOriginalQPackets.plot D u
  wire i := roundTrips (stencil D u i).toList
  height i := 2 * ((stencil D u i).toList.map (fun y => (outward y).length)).sum
  born i := Finset.mem_union_left _ ((ActualRunQlocalNativeTuple.positions D).mem i)
  visits i := by
    rw [plot]
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    rw [add_comm]
    exact covers _ (Finset.mem_toList.mpr hy)
  room i := (length _).le

theorem located (i : V) : (paper D u).origin i = ActualRunQlocalNativeTuple.root D i ∧
    (paper D u).support i = ActualOriginalQPackets.plot D u i ∧
    ((paper D u).wire i).length = (paper D u).height i :=
  ⟨rfl,rfl,length _⟩

end YM.Integration.WilsonOriginalProjectedCurvaturePassport
