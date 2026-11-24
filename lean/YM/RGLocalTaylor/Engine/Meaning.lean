import YM.RGLocalTaylor.Engine.Render

/-!
# Read glyphs at the actual sector moment

Here we make sure the analytic reading of the any-power `Insert`
aperture is available as an integral in the one physical sector. Equality
with true tag/sector law at that point with no exceptional set of sector
points discarded. This doesn't grant compatibility of other angles/scales.
This moment uses the original holding and Gaussian data with flags **planted**.
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

namespace Insert
abbrev momentSpace (_X : Coat T F) := F.Slice G × Air f G
def joint (r : Insert T) (X : Coat T F) (z : momentSpace X):= r.value (X.wrapY z.1) z.2
abbrev moment (X : Coat T F) := (F.order G).prod X.dice
end Insert

namespace Fits
open Insert
variable {p : Molecule S} {r : Insert T} (h : Fits H r (H.unionP p) j) (hX : X.x=s) (hK : X.width=o.K)
    (hχ : X.χ=χ) {N : Captain H j C' d v Y A b q B η n χ}
include h hX hK hχ N

lemma onMoment (hp:X.manifest) : Integrable (joint r X) (moment X) := by
  let f:ℝ → Config G c:=fun _=>X.V; have hv : Mode f 0 j v := ⟨N.position.le, fun i=> a_oneB G _ N.position.le⟩
  have hF:= N.oboe.flow F X hX hχ hK hp ℝ f 0 rfl hv
  obtain ⟨C,hC,hL⟩:= (h.near X hX hK hp ℝ f 0 N.oboe.conduit N.oboe.mode hF).post
  have hm : Measurable (joint r X):= h.along (V:=fun _=>X.V) X hX hK (momentSpace X) measurable_const measurable_fst measurable_snd
  have hh u := (hL.self_of_nhds u).bound; refine (memLp_top_of_bound hm.aestronglyMeasurable _ (Eventually.of_forall
    (fun w => show ‖joint r X w‖≤ C from ?_))).integrable le_top
  have he : X.V=(X.wrapY w.1).V:=rfl
  unfold joint
  have hw := hh w; rw [Insert.tracking,show f 0=(X.wrapY w.1).V from rfl, Silica.home (X.wrapY w.1) N.oboe.conduit w.2 H.laws.intake.positive] at hw
  exact hw

lemma preGauge_meaning (hF:authorized H p) (ht : (roster p).flags=∅) (hh:Healthy (Pressure.temp s) (H.unionP p) X.V) :
    r.preGauge H p X=likely fun i:S.Choices=>let Z := (planted X p).taggedL i; ∫ v,r.joint Z v ∂moment Z := by
  let f:ℝ → Config G c:=fun _=>X.V; have hv : Mode f 0 j v := ⟨N.position.le, fun i=> a_oneB G _ N.position.le⟩
  rw [show r.preGauge H p X=r.inTags H p X from (h.legitimate hX hK ht hh hχ hv rfl (Ξ:=N)).self_of_nhds]
  change r.inTags H p (vary X (f 0))= _; rw [h.atTags hX hK ht hh hF]
  apply congr_arg likely; funext i
  let Z:= (planted X p).taggedL i; change r.onSlice (podium _ _ _ Z.B) Z= _
  have hp : Z.manifest:= planted_valid X p
  exact (h.actual_slice (X:=Z) hX hK (H.laws.data.localP F Z hX hK hp).sails.fullC _ (Finset.Subset.refl _)).trans (integral_prod _ (h.onMoment (X:=Z) (N:=N) hX hK hχ hp)).symm

omit hX hK hχ in
lemma exact_meaning (U : Config G c) (hF : authorized H p) (ht : (roster p).flags=∅) (hh:Healthy (Pressure.temp s) (H.unionP p) U) :
    r.onLog H χ p U=likely fun j:Greenbelt.Reserve S=> let Z:= prism T s χ o.K U (Greenbelt.allot j); likely fun i:S.Choices=> let Y:= (planted Z p).taggedL i; ∫ v,r.joint Y v ∂moment Y:=
  congr_arg likely (funext fun j:Greenbelt.Reserve S=> h.preGauge_meaning (X:=prism T s χ o.K U (Greenbelt.allot j)) (N:=N) rfl rfl rfl hF ht hh)
end Fits
end YM.RGLocalTaylor
