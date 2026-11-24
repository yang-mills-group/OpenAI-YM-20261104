import YM.RegulatorIR.Gain.OnAir
import YM.RegulatorIR.Tape.Poles

/-!
# Grip schedule release. Uniform perStep phase relation

Connected tests still rely only on a conditional estimate. Kinetic/vacuum
orthogonality budget derived here from itinerary even though layers not acausal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Taping
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W:Type} {u b p j k s m:ℕ}{M: W→ℕ}{n:Page M→Side} {L:Meter W}{D:Choice M}
variable {S:Heir n G} (R: Reel S)

def taskK (u:ℕ)(S:Heir n G)(w: Flap M):= Tariff.native (S.ceiling w) (S.high w) u
def jobO (u:ℕ)(S:Heir n G)(w:Flap M):= Tariff.onFold _ (S.hp w.volW) (S.ceiling w) (S.high w) u

-- Keep small pre cost visible. no wire covariance asserted, need cover equations.
structure Inspires (J:Flap M→Layer (Foot G) (Foot G))(V:Flap M→ Bride G)(S:Heir n G) : Prop where
 tune w: S.sight w=grain (S.frames w) (J w) (V w)
-- step cost constants provided separately from recursions

structure Azur (R: Reel S)(J:Flap M→ Layer (Foot G) (Foot G))(V:Flap M→ Bride G) (k:ℕ)(L: Meter W)(c: Flap M→ℝ≥0∞):Prop where
 run : Halo.Common R
 depth : Poly L fun w=> (M w:ℝ≥0∞)
 caps : ∀ w,c w ≤1
 drift w: R.Dtr w= Gain.valve (J w) (V w)
 carryI : ∀ w:Flap M, Layer.Sym (S.maps w.prev) (S.maps w.next) (J w)
 carryP : ∀ w:Flap M, Rune (S.maps w.next) (n w.prev) (V w)
 prepaid w : Layer.row (J w) (taskK k S w) (S.maps w.prev).pos (S.maps w.next).pos (c w)
 other : ∃ a,Poly (flapL M L) a ∧ ∀ w, Layer.row (V w) (taskK k S w) (pointS (S.l w.prev)) (S.maps w.next).pos (a w)

namespace Azur
variable {R}
variable {J:Flap M → Layer (Foot G) (Foot G)} {V:Flap M → Bride G}
variable {c: Flap M→ℝ≥0∞}
variable (C: Azur R J V k L c) (P: Inspires J V S)
include C
lemma invoke (v:Flap M) : Passport (S.maps v.prev) (S.maps v.next) (S.frames v) (J v) (V v):=by
 obtain ⟨t,h,H⟩:=C.other
 exact ⟨(R.meanF _).trans (C.drift _ ▸ rfl), C.carryI _, C.drift _ ▸ (R.moduli _).sym.2.2.1, C.carryP _, billed_supp (C.prepaid _) (ne_top_of_le_ne_top ENNReal.one_ne_top (C.caps _)),billed_supp (H v) (h.cost v)⟩
lemma scale_down {k':ℕ}(h:k'≤ k): Azur R J V k' L c:=by
 obtain ⟨r,hr,hv⟩:= C.other;exact { C with other:= ⟨r,hr,fun w=> Layer.row_mono (A:=taskK k S w) (fun _ _=>Tariff.moment_mono (S.high w) h dist_nonneg) (hv w)⟩, prepaid:= fun w=> Layer.row_mono (A:=taskK k S w) (fun _ _=>Tariff.moment_mono (S.high w) h dist_nonneg) (C.prepaid w) }
include P

lemma ground (w): (S.sight w).Ground:=by rw [P.tune];exact Gain.braked (S.frames w) (C.invoke w) (R.even w.prev) (R.phase w.prev) (R.realms w.prev) -- arg order check
lemma diagonal {u:ℕ}(h:u≤k): S.Lead u c:=by
 refine { cap:=C.caps, down:=fun w=>?_ };rw [P.tune]
 exact Gain.zoom _ _ _ _ ((C.scale_down h).prepaid w)

lemma bolts (i:ℕ) : SmoothPrice (flapL M L) (taskK k S) (fun w:Flap M=> (S.maps w.prev).pos) (fun w=> (S.maps w.next).pos) (fun w=>(S.sight w).space) i:=by
 obtain ⟨x,hx,h⟩:=C.other; have hp:Poly (flapL M L) c := Poly.mono (Poly.oneQ _) C.caps
 let b:ℝ≥0∞:=2^k; have h': b≠⊤:=by unfold b;finiteness
 have hg:=Poly.add hp ((Poly.standard _ h').mul hx)
 refine ⟨_,(Poly.standard _ (Gain.hatch_fin G i)).mul (hg.powQ (i+1)),?_⟩; intro w z
 have hf:= C.prepaid w
 rw [R.realms w.prev] at hf; change row _ _ (localL (S.l w.prev)) _ _ at hf
 -- simplify
 dsimp only; rw [P.tune w]; change markQ ((Premium.rooted (taskK k S w) ((S.maps w.prev).pos z)).uses (S.maps w.next).pos) _ ≤ _
 have ht:= stride (J w) (V w) (S.hl w.prev) (S.climb w) _ hf (h w) z
 change markQ ((Premium.rooted (taskK k S w) ((S.maps w.prev).pos z)).uses (S.maps w.next).pos) (Gain.loom (pet G z.2 i) (tubeL (J w) (V w) z.1)) ≤ _
 rw [R.realms w.prev]; exact (loom_cost _ _ _ _ _ ht).trans (mul_le_mul_left (hatch_ge G z.2 i) _)
lemma springs (i:ℕ) : SmoothPrice (flapL M L) (jobO k S) (fun w: Flap M=> (S.maps w.prev).atO) (fun w=>(S.maps w.next).atO) (fun w=>(S.sight w).run) i:= by
 obtain ⟨x,hx,h⟩:= C.other; have hp: Poly (flapL M L) c:=Poly.mono (Poly.oneQ _) C.caps
 let b:ℝ≥0∞:=2^k; have h': b≠⊤:=by unfold b;finiteness
 have hg:=Poly.add hp ((Poly.standard _ h').mul hx)
 refine ⟨_, (Poly.standard _ (Gain.hatch_fin G i)).mul (hg.powQ (i+1)),?_⟩;intro w z
 have hf:=C.prepaid w; rw [R.realms w.prev] at hf;change row _ _ (localL _) _ _ at hf
 dsimp only; rw [P.tune w]; change markQ ((Premium.rooted (jobO k S w) ((S.maps w.prev).atO z)).uses (S.maps w.next).atO) (localize (A:=S.maps w.prev) (B:=S.maps w.next) _ _ z i) ≤ hatchV G i * _; rw [R.realms w.prev]
 apply le_trans (loom_cost (pet G z.2 i) (K:=tubeO (wrapL _ (S.maps w.next) (J w)) (scene (V w) (S.maps w.next)) z.1) _ _ _ (strideO (J w) (V w) (S.hl w.prev) (S.climb w) (S.hp _) (R.even _) (R.phase w.prev) z hf (h w)))
 exact mul_le_mul_left (hatch_ge ..) _

lemma era (p:ℕ)(h:Halo.Aug.Amenities S L p k): S.Primitive L p k:=by
 exact {
    depth:=C.depth
    line:=h.line
    drift:=h.mean
    add_cost:=h.budget
    deckLine:=Halo.hort R
    deckDrift:=Halo.suitable R,deckAdd:= fun w i j _=>Halo.natural_o R w i j,grade:= Halo.essential R,ground:=C.ground P
    prices:=fun _ hk i _=>(C.scale_down hk).bolts P i,charges:=fun _ hk i _=>(C.scale_down hk).springs P i }
end Azur
end YM.RegulatorIR.Taping
