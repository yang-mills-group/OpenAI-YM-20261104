import YM.OPE.Compatible.Maestro.Snap
/-!
# Clocked prices along any rooted growth, with specified precision
of offset lattice.

Uniformity over layouts satisfying explicit lifetime bounds. Same proof for cut of strict active subset with intermediate labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot Series
variable {G:Gauge}{C:Family G}{I V:Type}{φ:Filter I}{T r : I→ℝ}{q:I→ℕ}{b n:ℕ}
variable [PartialOrder V][Fintype V][OrderBot V](D:Origin V){η : ℝ}
variable {s:I→V→ℝ} {X:I→V→E4} {M e:ℝ} {Q:Finset V}
-- series prices still from geometry at visible active subset. ignore others.
structure Glowing (D:Origin V)(Q:Finset V)(φ:Filter I)(T:I→ℝ)(s:I→V→ℝ)(η:ℝ): Prop where
    crowned : Crown Q
    ray : Tendsto T φ atTop
    positive : 0<η
    fade v : v∈Q→ Tendsto (fun i=> s i v) φ (𝓝[>]0)
    charge v : v∈Q→ Score φ T (fun i=> -Real.log (s i v))
    dim : ∀ᶠ i in φ,∀ v∈Q,∀ u,u≤v→ s i v≤ s i u
variable (hG:G.Simple)(A:Allot C) (h: Glowing D Q φ T s η)
-- two clocks. aperture offset parent (leaf stand begins at search+1 to retain Blade). internal j may m x if not eligible.
def schedule (C:Family G)(b:ℕ)(η:ℝ)(s:V→ℝ)(v:V):= closeK C b η (s v)
def scopeTick (C:Family G)(b L:ℕ)(η:ℝ)(T:ℝ)(s:V→ℝ) (v:V):= resolution C b L η (s (par D v)) T
def aperture (C:Family G)(b L:ℕ)(η:ℝ)(T:ℝ)(s:V→ℝ) (v:V):= (scopeTick D C b L η T s v)+1
set_option quotPrecheck false
variable (b d:ℕ)
local notation "k"=> fun i=> schedule C b η (s i)
local notation "K"=> fun i=>scopeTick D C b d η (T i) (s i)
local notation "a!"=> fun i=> aperture D C b d η (T i) (s i)
lemma finish_aperture (v:V)(i:I): finishAt D (k i) v ≤ a! i v:= (le_max_left ..|>.trans (Nat.le_succ _))
include h
lemma parent_middle {x:V}(hx:x∈allUp D Q) : par D x∈Q:= (Finset.mem_union.mp hx).elim (h.crowned.roots (par_le D x)) (fun hi=>((on_brim ..).mp hi).2.2)
include hG A
lemma lives {v:V}(hv:v∈Q): Tendsto (fun i=> k i v) φ atTop:= elevated hG A b h.positive (h.fade v hv)
lemma thermal {v:V}(hv:v∈Q): Round φ T (fun i=> β C (k i v)) := epoch_score hG A b h.positive (h.fade v hv) h.ray (h.charge v hv)
lemma stands {v:V}(hv:v∈Q): Round φ T (fun i=> C.S.a (k i v)/s i v) := arrival_price hG A b h.positive (h.fade v hv) h.ray (h.charge v hv)
-- order dependency fix
lemma series_angle : ∀ᶠ i in φ,Series Q (k i):=by
    have hp:= (eventually_all_finset Q).mpr (fun v hv=> downscopes (C:=C) b h.positive (h.fade v hv) 0);
    filter_upwards [hp,h.dim] with i hi hm; refine ⟨h.crowned,fun v u he hq=>?_⟩
    have hv':= hi v (h.crowned.roots he hq); have hu':= hi u hq; have hk:=wins (b:=b) hG A (mul_pos h.positive hv'.1) ⟨0,hv'.2⟩; exact (wins (b:=b) hG A (mul_pos h.positive hu'.1) ⟨0,hu'.2⟩).2 _ ((mul_le_mul_of_nonneg_left (hm _ hq v he) h.positive.le).trans hk.1)
lemma climb {v:V}(hx:v ∈allUp D Q) : Tendsto (fun i=> K i v) φ atTop ∧ Round φ T (fun i=> β C (K i v))∧ Round φ T (fun i=>C.S.a (K i v)/s i (par D v)):=by
   have hp:= parent_middle _ h hx; exact resolution_cost (L:=d) (b:=b) (h.fade _ hp) hG A h.ray (h.charge _ hp) h.positive
lemma arrive {v:V}(hx:v∈allUp D Q):
    Round φ T (fun i=> β C (a! i v))∧ Round φ T (fun i=>C.S.a (a! i v)/s i (par D v)):=by
    obtain ⟨hh,hv,ht⟩:= climb D hG A h b d hx; let f i:= K i v; let g i:= extent C (f i); have hh':Round φ T g:= Round.if_inv (Eventually.of_forall fun i=> zero_lt_two.trans_le (extent_two ..)) (hv.up.pointwise (Eventually.of_forall fun i=> A.block_cheap _) (Eventually.of_forall fun i=> zero_le_two.trans (extent_two ..))) h.ray (Eventually.of_forall fun i=>one_le_two.trans (extent_two ..))
    refine ⟨stepβ A hG h.ray hv.up,(ht.div hh').adjust ?_⟩; filter_upwards with i; change C.S.a (f i)/_ /_=C.S.a (f i+1) /_; rw [C.S.a_step]; unfold g extent; ring -- unfold precedence
omit A hG
lemma adjusted_to_grid {v:V}(hx:v∈allUp D Q): ∀ᶠ i in φ,C.S.a (a! i v) ≤ s i (par D v)/T i^d:= (below_resolution (C:=C) (b:=b) (L:=d) (η:=η) (h.fade _ (parent_middle _ h hx)) h.ray).mono (fun _ hi=> (C.S.strictAnti.antitone (Nat.le_succ _)).trans hi)
end YM.OPE.Arboreal
