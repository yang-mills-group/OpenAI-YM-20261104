import YM.RGLocalTaylor.Engine.Insert

/-! Native log/packet heads are licensed Taylor insertions.
(Generalizes parts of `Paisley.thatch` and `Ambit.thorn`: use the same
inventory as all the other heads.) -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

/-- The native E6 *individual*, unmasked, including its original tag,
profiles, sector conventions and fine-link derivatives; for regular identities.
(Here "unmasked" means before the coarse output mask; no change to the input
kernels!) Applied to the full-dimensional extended mean/Gaussian argument. -/
def leg (_H : Cash W s μ L Q o C T R) (p : Finset ℕ) (i : Head S) : Insert T where
  value X z :=
    let u := worldZ X R.beta z
    ember X o.a R W Q.table u (X.input u) z p Q.halo i

-- Qualitative part of the local derivative estimates, including through the
-- variable-holding transform with its protected profiles.
private lemma zest_leg (p : Finset ℕ) (i : Head S) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {V : E → Config G c} (hX : X.x=s) (hg : Glass P X V x j W)
    (hA : Canary G A b) (hb : 8 * o.a * Pressure.fiery G s L ≤ A/2) :
    Zest ((leg H p i).tracking A R.beta X V) x j := by
  let I := F.Slice G × Air f G
  let F' (t : I) := X.wrapY t.1
  let Q' (t : I) := worldZ (F' t) R.beta t.2
  let v t y := steer (F' t) A (fun i => prune A (Q' t i)) (V y)
  let Z t y := vary (F' t) (V y)
  let K t y := sweepZ (Z t y) R.beta (v t y)
  have hr : Room P S T X.x := hX.symm ▸ H.laws.data.room
  have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
  have hL : X.t=Pressure.fiery G s L := by unfold Coat.t; rw [hX,H.laws.data.funds.length_eq]
  have ha : 0 < o.a*X.t := mul_pos o.large hr.fiery
  rw [← hL] at hb
  have hv : Zest v x j := (hg.foreshadow (Y:=Prod.fst) Q' hA).1
  let L : Directions G f →ₗ[ℝ] Air f G := {
    toFun t:= WithLp.toLp _ (stand t)
    map_add' _ _:= rfl
    map_smul' _ _:= rfl }
  have hK : Zest K x j :=
    (((hv.plusminus (hg.settles (Y:=Prod.fst) hr)).scalar (gStep R.beta)⁻¹).replay L.toContinuousLinearMap)
  apply (hg.glassy (fun t=> (F' t).input (Q' t)) (Y:=Prod.fst) hr v hv he p Q.halo ha (hL.symm ▸ H.laws.data.covers) Q.table_exists i hK).congr
  obtain ⟨_,hf⟩:= hg.sails
  filter_upwards [Silica.nearby X hA hg.lifts hf,hg.brews.1] with y hy hm t
  let D := course (F' t) A R.beta t.2 (V y)
  let u := steer (F' t) A (Q' t) (V y)
  let u' := v t y
  let Z' := Z t y
  have hr' : Drivable (F' t) A b (V y) := ⟨hy.good⟩
  have hk : Transfer Z' u u' (4*o.a*X.t) := ⟨(fruit (F' t) hA (V y) (Q' t) (a:=4*o.a*X.t) (by nlinarith only [hb,hA.warm])).both⟩
  have hv := conquered (F' t) hA (V y) (Q' t) hr' (show 0<o.a*(F' t).t from ha) hb
  have hx:= (plastic (X:=Z') hv ha).reeled hr W Q.table p Q.halo he i D
  change ember Z' o.a R W Q.table u' ((F' t).input (Q' t)) _ p Q.halo i =
    ember Z' _ _ _ _ (worldZ Z' R.beta D) (Z'.input (worldZ Z' R.beta D)) D _ _ _
  rw [show worldZ Z' R.beta D=u from Silica.proceeds (F' t) _ he.positive _ _]
  exact (hx.trans (Transfer.carries Z' hk ha hr hm _ _ _ _ Q.halo _ i)).symm

lemma fits_leg (H : Cash W s μ L Q o C T R) (p : Finset ℕ) (i : Head S) (j : ℕ) :
    Fits H (leg H p i) (H.supportP i) j := by
  constructor
  · intro F X X' hX hK Y z z' hh hB
    have hv : Borough X X' Y z z' p p R := ⟨hB.toVillage,hB.airs,fun _ _=>Iff.rfl⟩
    have hy : areas R T Q.halo X.B i ⊆ Y := by unfold Coat.B; rw [hX]; exact hh
    have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
    have hr : Room P S T X.x := hX.symm ▸ H.laws.data.room
    have hb:= (hv.rooms hr R.beta).preserve hr Q.buys he o.a W Q.table hv hy
    dsimp only at hb; rwa [X.oldysis he.positive,X'.oldysis he.positive] at hb
  · intro F X hX hK E _ V Z z hV hZ hz
    exact bornB X (show ShellAccess S G X.x W X.width o.γ from by rw [hX,hK]; exact H.laws.data.access)
      (hX.symm ▸ H.laws.intake) Q.table_exists hV hZ hz o.a Q.halo p i
  · intro F X hX hK h z w
    have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
    have hb : ShellAccess S G X.x W X.width o.γ := by rw [hX,hK]; exact H.laws.data.access
    have hs : X.t=Pressure.fiery G s L := by unfold Coat.t; rw [hX,H.laws.data.funds.length_eq]
    have hr : Room P S T X.x := hX.symm ▸ H.laws.data.room
    dsimp only [leg]
    rw [Stained.flight X z he.ready hb]
    exact Stained.fights X z hb he Q.halo p Q.table_exists (mul_pos o.large hr.fiery) (hs.symm ▸ H.laws.data.covers) h _ _ _
  intro F X hX _ _ E _ _ _ V x A b hA ha hp
  exact zest_leg p i hX hp hA ha

/-- Native integrated kernel insert. -/
def native (H : Cash W s μ L Q o C T R) (p : Molecule S) : Insert T :=
  Insert.joined p (leg H (own p))

lemma fits_native (H : Cash W s μ L Q o C T R) (p : Molecule S) (j : ℕ) :
    Fits H (native H p) (H.unionP p) j := by
  exact Fits.joined fun i hi => (fits_leg H (own p) i j).bigger (subset_biUnion_of_mem _ hi)

lemma native_value (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) (z : Air f G) :
    (native H p).value X z = Polar.floating X o.a R W Q.table z (own p) Q.halo p := rfl
end YM.RGLocalTaylor
