import YM.GapsContact.Slab.Station
import YM.TraceExtension.Atlas.Global
import YM.OPE.Levy.Panel
/-!
# Measuring norm in the unselected theory

Use the norm of this two-point function as the common positive price, not a fitted inverse in
an unrelated cutoff frame. (Definiteness here needed only eventually at small real distances.)
Once canonical measuring-scale matching on some horizon has been proved in another frame on
this same theory, it suffices to budget these matrix entries to use all our analytic estimates
there as well.

Uses actual leading Euclidean comparison along `Scribe` in its own frames; needs ONLY two
points. No assumptions on Wightman spectrum at high frequencies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Ascent
open Function Filter Set Extraction Table Climb Spec MeasureTheory Trace Trace.Pilot
open Push.FiniteDetection.Free Trace.Terrace Trace.Over Next.UVStress MergeProof.East OPE.Levy
open Analysis Ward
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff

variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F : Final C f S) (d n : ℕ) (hG:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Z:Trace.Terrace.Arch C}
local notation "S'"=> Climb.Bel C.book

def valTwo {L:Register G} (S : Table L) (d:ℕ)(x:Points 2)(u v:S.Field d) :=
   S.classMoment S (fun _ : Fin 2=>d) x ![u,v]

abbrev flipField (u:S.Field d) := S.mirror F.room.kernel.spin d (Signed.mirror timeAxis) (S.conj F.room.kernel.spin d u)

def cost (r:ℝ) (v:S.Field d) : ℝ := Real.sqrt ‖valTwo S d (r • detectors) v (flipField F d v)‖
lemma cost_pos (r:ℝ)(v:S.Field d) : 0 ≤ cost F d r v := Real.sqrt_nonneg _

lemma cost_hom (r:ℝ) (c:ℂ) (u:S.Field d): cost F d r (c • u)=‖c‖*cost F d r u:= by
  let M:=linear₂ (S.classMoment S (fun _ : Fin 2=>d) (r • detectors))
  have he : flipField F d (c • u)=star c • flipField F d u:= by
    unfold flipField; rw [LinearMap.map_smulₛₗ,map_smul]; rfl
  unfold cost; rw [he]
  change Real.sqrt ‖M (c • u) (star c • flipField F d u)‖ = ‖c‖*Real.sqrt ‖M u (flipField F d u)‖
  rw [M.map_smul,LinearMap.smul_apply,(M u).map_smul,norm_smul,norm_smul,norm_star,← mul_assoc,← sq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]

lemma cost_zero (r:ℝ): cost F d r 0=0:=by have h:= cost_hom F d r 0 0; simpa using h

-- analytic compacta point comparison only on Euclidean sets from the supplier
variable (h : StarPath f H J F.room.kernel 𝓛)
set_option quotPrecheck false
local notation "D" => (Climb.Bel C.book).Field d
local notation "P" => valTwo S d
local notation "Q" => valTwo (S') d
local notation "f₂" => reflect (C:=C) d
include hG h
lemma couple (u v:D) {R : Set (Points 2)} (hR:IsCompact R)(hs:R ⊆ conf _) :
    ∀ ε:ℝ,0<ε→∀ᶠ i in atTop,∀ x∈R,
      ‖valTwo S d (J.r i • x) (J.U i d u) (J.U i d v)-valTwo (S') d x u v‖≤ε := by
  obtain ⟨T,-,-⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  let t:Caps 2:=fun _=> d; let y:Ribbon (Bel C.book) t:=![u,v]
  let K i:= tested (J.r i) (isoPanel J i) (hang t y)
  let L:= disc (hang t y)
  intro ε he; filter_upwards [travels_jet F.room.kernel F.phase.transport.derivatives H T.lit.pales J h.approach (fun _ => y) y (fun _=> tendsto_const_nhds)
      0 R hR hs ε he] with i hi x hx
  specialize hi x hx
  rw [show valTwo S d _ _ _=K i x from ?_]; swap
  · unfold K tested valTwo disc useAt; apply DFunLike.congr_arg; funext j; fin_cases j<;> rfl
  change ‖K i x - L x‖ ≤ ε
  change ‖iteratedFDeriv ℝ 0 (K i) x - iteratedFDeriv ℝ 0 L x‖ ≤ ε at hi
  rwa [show (iteratedFDeriv ℝ 0 (K i) x - iteratedFDeriv ℝ 0 L x)= iteratedFDeriv ℝ 0 (K i-L) x by ext; simp,
    norm_iteratedFDeriv_zero,Pi.sub_apply] at hi

variable {E:Type*}{l:Filter E}{m:E→ℕ}{x:E→Points 2}{X:Points 2}
variable {u v:E→(Bel C.book).Field d}{u₀ v₀:(Bel C.book).Field d}
variable (hm:Tendsto m l atTop)(hx:Tendsto x l (𝓝 X))(hX:X∈conf _)
include hm hx hX in
private lemma point (u v:D):
    Tendsto (fun i=> P (J.r (m i) • x i) (J.U (m i) d u) (J.U (m i) d v))
      l (𝓝 (Q X u v)) := by
  let y(s : Points 2):= valTwo (S') d s u v
  let K(s : E):= valTwo S d (J.r (m s) • x s) (J.U (m s) d u) (J.U (m s) d v)
  have hp:Tendsto (y ∘ x) l (𝓝 (y X)):= ((smoothDisc H.smooth (fun i:Fin 2=> (⟨d,(![u,v]:Fin 2→D) i⟩: (Bel C.book).Tag))).continuousOn.continuousAt ((conf_open 2).mem_nhds hX)).tendsto.comp hx
  have hh:Tendsto (K-(y∘x)) l (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr; intro ε he
    obtain ⟨R,hR,hsub,hW⟩:= exists_compact_subset (conf_open _) hX
    filter_upwards [hx.eventually (mem_interior_iff_mem_nhds.mp hsub),hm.eventually (couple F d hG h u v hR hW (ε/2) (half_pos he))] with i hi hj
    rw [dist_zero_right]; exact (hj (x i) hi).trans_lt (half_lt_self he)
  change Tendsto K l (𝓝 (y X))
  rw [← sub_add_cancel K (y ∘ x)] -- occurrence?
  exact (zero_add (y X)) ▸ hh.add hp

-- leading reduction with moving normalized labels. Same route as in `OPE.Levy.Panel.joint`.
set_option maxHeartbeats 1500000 in
lemma couple_seq (hm:Tendsto m l atTop)(hx:Tendsto x l (𝓝 X))(hX:X∈conf _)(hu:Tendsto u l (𝓝 u₀))(hv:Tendsto v l (𝓝 v₀)):
    Tendsto (fun i=> valTwo S d (J.r (m i) • x i) (J.U (m i) d (u i)) (J.U (m i) d (v i))) l (𝓝 (valTwo (S') d X u₀ v₀)) := by
  let M (i:E) := linear₂ (S.classMoment S (fun _ : Fin 2=>d) (J.r (m i) • x i))
  let A (i:E) (u:D):= (M i (J.U (m i) d u)).comp (J.U (m i) d).toLinearMap
  let K:=linear₂ ((S').classMoment (S') (fun _=>d) X)
  refine YM.Dash.arcing (W:=fun i=> (A i (u i)).toContinuousLinearMap) (X:=LinearMap.toContinuousLinearMap (K u₀)) (?_) hv
  refine YM.Dash.fit_plane _ _ (fun p:D=>?_)
  let a i:= ((M i).flip (J.U (m i) d p)).comp (J.U (m i) d).toLinearMap
  exact YM.Dash.arcing (YM.Dash.fit_plane a (K.flip p) (fun u:D=> point F d hG h hm hx hX u p)) hu

lemma cost_seq {s:E→ℝ}{s₀:ℝ} (hm:Tendsto m l atTop)(hu:Tendsto u l (𝓝 u₀))(hs:Tendsto s l (𝓝 s₀))(hs₀:0<s₀): Tendsto
    (fun i=>cost F d (J.r (m i)*s i) (J.U (m i) d (u i))) l
    (𝓝 (Real.sqrt ‖valTwo (S') d (s₀ • detectors) u₀ (reflect (C:=C) d u₀)‖)) := by
  have p := couple_seq F d hG h hm (hs.smul_const detectors) (Work.A05.smul_conf hs₀ detectors_in) hu (reflect_limit (C:=C) d hu)
  apply (p.norm.sqrt).congr'; filter_upwards [hm.eventually (h.units d)] with i hi
  obtain ⟨he,-⟩:=hi; have he' : Coherent (Maxwell.Free.spin_free C.labels) F.room.kernel.spin d (J.U (m i) d):=he
  change Real.sqrt ‖valTwo S d _ _ (J.U (m i) d (reflect (C:=C) d (u i)))‖=_
  unfold cost reflect flipField; rw [he'.signed,he'.stars,mul_smul]
end YM.GapsContact.Ascent
