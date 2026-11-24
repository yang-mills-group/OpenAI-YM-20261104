import YM.Integration.WilsonRootedMayerHull

/-! Physical numerator and its surviving original Mayer grades on one joint fine coordinate set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedMayerOriginal

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Lotus Daisy RGLocalTaylor RGLocalTaylor.Mayer
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}
variable {K θ e uJ vJ discount : ℝ}

/-- The whole native physical team payment reads this same single joint set. Only its own
coarse support is required healthy when the original chart is evaluated. -/
theorem team (H : Cash W s μ L Q o C T R) (prior : Team R) (p : Molecule S)
    (all : prior.signs S⊆p) (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K)
    (hm : X.manifest) (inside : Healthy (Pressure.temp s) (H.unionP p) X.V)
    (y : F.Slice G) (z : Air f G) :
    let E:=WilsonRootedMayerHull.coordinates H p X
    prior.into X W o.a Q.table (own p) Q.halo p (y,z) =
      prior.into X W o.a Q.table (own p) Q.halo p (y,Pond.spill E (Pond.swim E z)) := by
  intro E
  exact (Laminate.into_coins all hx hm inside _).trans ((WilsonRootedMayerHull.unexpanded H prior p
    X hx hw y z).trans (Laminate.into_coins all hx hm inside _).symm)

/-- Surviving orders bound the count of non-team vertices on the actual compatible component. -/
theorem room (prior : Team R) (p : Molecule S) {M : ℕ}
    (u : Decors (p\prior.signs S) M) (grade : decorOrder u≤M) :
    (p\prior.signs S).card≤M ∧ p.card≤(prior.signs S).card+M := by
  have h : (p\prior.signs S).card ≤ decorOrder u := by
    calc _ = ∑ _i : ↥(p\prior.signs S), 1 := by simp
         _ ≤ _ := Finset.sum_le_sum fun i _=>Nat.succ_le_succ (Nat.zero_le (u i).val)
  refine ⟨h.trans grade,?_⟩
  have h₁ := Finset.card_le_card (show p⊆prior.signs S∪(p\prior.signs S) by
    intro i hi
    by_cases h' : i∈prior.signs S
    · exact mem_union_left _ h'
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hi,h'⟩))
  exact h₁.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (h.trans grade) _))

/-- On an issued chart, every surviving actual planned product is exactly a function of
the projected original Gaussian and the single held original Haar field. -/
theorem planned (H : Cash W s μ L Q o C T R) (prior : Team R) (p : Molecule S)
    {M : ℕ} (u : Decors (p\prior.signs S) M) (grade : decorOrder u≤M)
    (N : Captain H j C' d v Y A b r B q n χ) (hG : Awning H N.conduit A b discount e uJ vJ k l)
    (hg : Q.goal L s ≤ K) (hT : Approved K θ j M) (start : Start (p\prior.signs S))
    (X : Coat T F) (inside : Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx : X.x=s) (hw : X.width=o.K) (hχ : X.χ=χ) (hm : X.manifest)
    (y : F.Slice G) (z : Air f G) :
    let E:=WilsonRootedMayerHull.coordinates H p X
    Mayer.planned H p u (Laminate.partner prior H) X (y,z) =
      Mayer.planned H p u (Laminate.partner prior H) X (y,Pond.spill E (Pond.swim E z)) := by
  intro E
  have eq:=Mayer.physical_plan u sdiff_subset grade N hG hg hT
    (Laminate.partner prior H) start inside hx hw hχ hm
  exact (congrFun eq _).symm.trans ((WilsonRootedMayerHull.decorated H prior p u X hx hw y z).trans (congrFun eq _))

end YM.Integration.WilsonRootedMayerOriginal
