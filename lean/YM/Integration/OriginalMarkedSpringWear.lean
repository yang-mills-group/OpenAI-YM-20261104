import YM.Integration.ActualRunSpring
import YM.Integration.OriginalMarkedSignedCutoff

/-! The original finite marked Taylor expansion on the actual incoming and
outgoing fields of one selected physical Spring. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedSpringWear
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker RG.Supply
open Extra.Trajectories PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Menu MergeProof.Accent MergeProof.Ribbon
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V I : Type} [Fintype V] [Fintype I]
    [Nonempty V] [DecidableEq V] {E : Census V}

omit [Nonempty V] in
private theorem carry {A B : Rep G n} (equal : A = B) (q : I → Menu.Hat E A)
    (o : V → Site n) (w : V → ℝ) (paid : Menu.Offer o q w A.p.B (A.p.supportExponent-4) 1) :
    ∃ r : I → Menu.Hat E B, GapsLocal.Full.given r 0 = GapsLocal.Full.given q 0 ∧
      Menu.Offer o r w B.p.B (B.p.supportExponent-4) 1 := by
  subst B
  exact ⟨q,rfl,paid⟩

abbrev Installed (run : Run G) {upper period level : ℕ} (below : level<upper)
    (packet : ActualRunSpring.Packet run upper period level below)
    (r : I → Menu.Hat E (packet.input packet.point.val)) (weights : V → ℝ)
    (sites : V → Site (run.alloy.B.a.S.side (level+1) period)) (degree : ℕ) : Prop :=
  GapsLocal.Full.Outfit (G:=G) (X:=run.metals) (D:=run.rolls) (A:=run.alloy) (R:=run.kit)
    (N:=upper) (m:=level) (n:=period) (l:=packet.lower) (v:=packet.upper) (Q:=packet.input)
    (ι:=I) (V:=V) (E':=E) packet.spring packet.point r weights (0 : V → ℂ) sites
    0 (Fintype.card V) degree (packet.spring.result packet.point.val) 0

private theorem enacted {metals : Org.Metals G} {rolls : Rolls metals.p} {atlas : Org.Alloy metals rolls}
    {factor : Roost.Factor atlas} {upper period level degree : ℕ} {lo hi : ℝ}
    {input : UVNext.CouplingReset.In atlas.B.a level period} (simple : G.Simple)
    (spring : Mallow.Spring factor upper level period lo hi input) (point : Set.Icc lo hi)
    (hats : I → Menu.Hat E (input point.val)) (weights : V → ℝ)
    (roots : V → Site (atlas.B.a.S.side (level+1) period))
    (marks : Mallow.RG12.Earned (markerBudget G) factor.shape atlas.delay) (below : level<upper)
    (arrives : Mallow.Arrives factor.shape atlas.delay)
    (sf : 100≤(atlas.B.a.budget (level+1)).supportExponent) (sc : 100≤(atlas.B.a.budget level).supportExponent)
    (ready : GapsLocal.Full.target 0 (Fintype.card V) degree≤atlas.B.a.clock.J (level+1))
    (occupancy : Extra.Multi.Occupancy ((atlas.B.a.clock.op level period).ratio.parent ∘ roots) (atlas.B.a.clock.J (level+1)))
    (price : Menu.Offer roots hats weights (input point.val).p.B ((input point.val).p.supportExponent-4) 1)
    (positive : ∀ i, 0<weights i) :
    GapsLocal.Full.Outfit spring point hats weights (0 : V → ℂ) roots 0 (Fintype.card V) degree (spring.result point.val) 0 := by
  have quiet (i : V) : weights i*‖(0 : V → ℂ) i‖≤0 := by simp
  have size (i : E.Mode) : i.val.card≤Fintype.card V := Finset.card_le_univ _
  exact GapsLocal.Full.wear (G:=G) (X:=metals) (D:=rolls) (A:=atlas) (R:=factor)
    (N:=upper) (m:=level) (n:=period) (l:=lo) (v:=hi) (Q:=input) (ι:=I) (V:=V) (E':=E)
    (a:=0) (b:=Fintype.card V) (d:=degree) (e:=0) simple spring point hats weights (0 : V → ℂ) roots
    marks below arrives sf sc ready occupancy (by simpa only [pow_zero] using price) positive quiet size

/-- The physical incoming roster is transported to the identical original Spring point. -/
theorem registered (run : Run G) (simple : G.Simple) {upper period level degree : ℕ} (below : level<upper)
    (marks : Mallow.RG12.Earned (markerBudget G) run.kit.shape run.alloy.delay)
    (sf : 100≤(run.alloy.B.a.budget (level+1)).supportExponent) (sc : 100≤(run.alloy.B.a.budget level).supportExponent)
    (ready : GapsLocal.Full.target 0 (Fintype.card V) degree≤run.alloy.B.a.clock.J (level+1))
    (roots : V → Site (run.family.side (level+1) period)) (weights : V → ℝ) (positive : ∀ i, 0<weights i)
    (occupancy : Extra.Multi.Occupancy ((run.family.path.levels.clock.op level period).ratio.parent ∘ roots)
      (run.family.path.levels.clock.J (level+1)))
    (hats : I → Menu.Hat E (run.family.path.rep upper period (level+1)))
    (offer : Menu.Offer roots hats weights (run.family.path.rep upper period (level+1)).p.B
      ((run.family.path.rep upper period (level+1)).p.supportExponent-4) 1) :
    let packet := ActualRunSpring.selected run upper period level below
    ∃ r : I → Menu.Hat E (packet.input packet.point.val),
      GapsLocal.Full.given r 0=GapsLocal.Full.given hats 0 ∧ Installed run below packet r weights roots degree := by
  let packet := ActualRunSpring.selected run upper period level below
  obtain ⟨r,he,hr⟩ := carry (n:=run.alloy.B.a.S.side (level+1) period) packet.fine hats roots weights offer
  refine ⟨r,he,?_⟩
  exact enacted simple packet.spring packet.point r weights roots marks below run.b.r sf sc ready occupancy hr positive

/-- Every signed compound mode is charged to strictly lower physical moments. -/
theorem priced (run : Run G) (simple : G.Simple) {upper period level degree : ℕ} (below : level<upper)
    (marks : Mallow.RG12.Earned (markerBudget G) run.kit.shape run.alloy.delay)
    (sf : 100≤(run.alloy.B.a.budget (level+1)).supportExponent) (sc : 100≤(run.alloy.B.a.budget level).supportExponent)
    (ready : GapsLocal.Full.target 0 (Fintype.card V) degree≤run.alloy.B.a.clock.J (level+1))
    (roots : V → Site (run.family.side (level+1) period)) (weights : V → ℝ) (positive : ∀ i, 0<weights i)
    (occupancy : Extra.Multi.Occupancy ((run.family.path.levels.clock.op level period).ratio.parent ∘ roots)
      (run.family.path.levels.clock.J (level+1)))
    (hats : I → Menu.Hat E (run.family.path.rep upper period (level+1)))
    (offer : Menu.Offer roots hats weights (run.family.path.rep upper period (level+1)).p.B
      ((run.family.path.rep upper period (level+1)).p.supportExponent-4) 1) :
    let fine := run.family.path.rep upper period (level+1)
    let op := run.family.path.levels.clock.op level period
    let F := op.push fine.beta (GapsLocal.Full.given hats 0)
    let g := Pert.Asymptotics.regulatorRun run.family upper period (level+1)
    ∃ kept : Config G (run.family.side level period) → Poly E,
      (∀ j, Integrable (fun U => (kept U).part j) (prior G _)) ∧ ∀ j U,
      Poly.toll weights j*‖(F U-kept U).part j‖≤(Real.exp (Fintype.card V*(Real.sqrt 2*g)^(degree+1))-1)*
        Poly.price weights (OriginalMarkedSignedCutoff.lower j (F U)) := by
  let packet := ActualRunSpring.selected run upper period level below
  obtain ⟨r,hr,h⟩ := registered run simple below marks sf sc ready roots weights positive occupancy hats offer
  obtain ⟨issued,claim⟩ := h.adapted
  have law := (run.makes.wilson.represents upper period level below.le).good
  change (run.family.path.rep upper period level).Lawful _ _ _ _ _ at law
  have nonneg : 0≤(run.family.path.rep upper period level).beta :=
    (Overlay.beta_positive (H:=run.family.path) run.makes.wilson below.le (p:=period)).le
  rw [packet.coarse] at law nonneg
  have beta := congrArg (fun A : Rep G (run.family.side (level+1) period) => A.beta) packet.fine
  have coupling : Pert.Asymptotics.regulatorRun run.family upper period (level+1)=
      GapsLocal.Vacuum.nativeG (packet.input packet.point.val).beta :=
    congrArg (fun b : ℝ => (Real.sqrt b)⁻¹) beta
  dsimp only
  rw [←hr,issued,beta,coupling]
  exact ⟨_,fun j => (Overlay.Bands.material _ claim.funded.1 claim.funded.2 law nonneg j).1,
    fun j U => OriginalMarkedSignedCutoff.proper_price claim j U⟩

end YM.Integration.OriginalMarkedSpringWear
end
