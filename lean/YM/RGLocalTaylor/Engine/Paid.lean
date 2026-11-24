import YM.RGLocalTaylor.Engine.Render
import YM.RGLocalTaylor.Engine.Roof

/-! # Actual priced integral of inserted pieces at every real healthy argument.

No `unforced` shortcut. Includes analytically extended clean-coarse germs of
regions containing a fine compulsory sector, as well as molecules with multiple
exceptional-warning, ordinary inherited-interaction or analytic occurrences.
The additional discount attached to each `Warning` in **each copy** of its first
molecule may now be spent at fixed Taylor demand while keeping all hard caps.
-/
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

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Awning
variable {e uJ vJ α weight discount : ℝ} {p : Molecule S} {f' : Insert T}
variable {N : Captain H j C' d v Y A b r B q n χ}
    (h : Awning H N.conduit A b discount e uJ vJ k l)
include h

lemma priced (hF : CoveredAt N.conduit f' p A weight α) (hz:0≤weight) (ha:1≤α)
    (hh : Fits H f' (H.unionP p) j) (he : (roster p).flags=∅) (U : Config G c)
    (hy:Healthy (Pressure.temp s) (H.unionP p) U) :
    Ore U (f'.onLog H χ p) v (speedBill e uJ α j * weight * (1+H.shapeW p)^(l+j) *
      (discount*N.conduit.rad)^(blaze p).card) j := by
  intro E _ _ _ V x hV hf
  let D := speedBill e uJ α j * weight * (1+H.shapeW p)^(l+j) * (discount*N.conduit.rad)^(blaze p).card
  have hD : 0≤D := by
    unfold D speedBill; have hu:= h.earn; have hb:=h.bSc; have hr:=N.conduit.awake; have he:=h.nonneg; have hv:=H.positive_volume p; positivity
  by_cases ht : authorized H p
  swap; · refine Brush.zi (Eventually.of_forall fun y=> f'.onLog_of_forbidden ht _) hD zero_le_one
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let X i := prism T s χ o.K U (Greenbelt.allot (S:=S) i); let f i V:=f'.preGauge H p (vary (X i) V)
  change Brush _ _ _ (fun y=> likely (fun i=> f i (V y))) _
  apply Captain.avgBrush
  intro i
  let K := planted (X i) p
  let I:= edgesM S (H.unionP p) (radiusB s); let P:= podium S G (H.unionP p) (radiusB s)
  let Z (q:S.Choices) y:= f'.onSlice P (vary (K.taggedL q) (V y))
  have hq(q:S.Choices) : Brush j D 1 (Z q) x := by
    let X' := K.taggedL q
    have hv' : X'.manifest:= planted_valid (X i) p
    have hw := N.oboe.flow _ X' rfl rfl rfl hv' E V x hV hf
    obtain ⟨g,hg,hb,hΓ⟩:= h.enhanced hF hz ha (X:=X') rfl rfl rfl hv' hy hf hV
    exact (((hh.reaches (X:=X') (I:=I) rfl hv' rfl hw N.oboe.conduit N.oboe.mode).1.buds g hg zero_le_one hb
      (Eventually.of_forall hΓ))).shimmy (hh.slideToCourse (X:=X') rfl hv' rfl hw N.oboe.conduit N.oboe.mode (H.unionP p) (Finset.Subset.refl _))
  refine (Captain.avgBrush Z D x hq).shimmy ?_
  exact (hh.legitimate (X:=X i) rfl rfl he hy rfl hf hV (Ξ:=N)).trans
    (Eventually.of_forall fun y=> hh.atTags (X:=X i) rfl rfl he hy ht (V y))

lemma ordinarySlice (hp : (roster p).flags=∅) (U : Config G c) (hy:Healthy (Pressure.temp s) (H.unionP p) U) :
    Ore U ((native H p).onLog H χ p) v
      (speedBill e uJ r j * N.conduit.meant p (l+j) * discount^(blaze p).card) j := by
  by_cases he : authorized H p
  swap
  · have he':0 ≤ speedBill e uJ r j := by unfold speedBill; have hv:= h.earn; have hb:=h.bSc; have hF:=N.conduit.active; positivity
    exact fun E _ _ _ _ _ _ _=> Brush.zi (Eventually.of_forall fun q=> Insert.onLog_of_forbidden he ..)
      (mul_nonneg (mul_nonneg he' (N.conduit.meant_nonneg ..)) (pow_nonneg h.nonneg _)) zero_le_one
  have ht:= he.2
  have hy' := h.priced (h.covered_native ht) (prod_nonneg fun i _ => N.conduit.tagged _) N.conduit.active (fits_native H p j) hp U hy
  rw [Utopia.meant,if_pos ((H.attends p).2 he.1),N.conduit.remixes]
  convert! hy' using 1; rw [mul_pow]; ring
end Awning
end YM.RGLocalTaylor
