import YM.RG3.Pan.Bolt

/-!
# Unmasked group payload via genuine small CURVATURE variables

On the physically tested region, and germ equality incl Wiggles that need
not preserve flag positions. No linearization used; include higher powers
from paths and their inverse chart. `palette` itself global even at switch.
All paths and faces fetched only on the patch for the corresponding
source root. Charge powers against polynomial stage costs (fixed order).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Lattice Wilson Function WilsonStartup Next.Rank.Spindle Filter RG
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {n : Side} {G : Gauge} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b k : ℕ} {o : Site n}
  {F : Config G n→E} {X : Support n}
local notation "hull" => Next.Rank.Spindle.patch
abbrev Palette (G : Gauge) (b:ℕ) := MapSet (Turn b) G

/-- ALL actual faces in the patch, oriented and based by the same canonical
paths. No threshold division. Unitary roots and gauge held. -/
def palette (b : ℕ) (o : Site n) (U : Config G n) : Palette G b:=(G.curvature ∘ registered b U o)

@[fun_prop] lemma palette_cont (G : Gauge) (b : ℕ) (o : Site n) : Continuous (palette (G:=G) b o):= continuous_pi fun i=> G.continuous_curvature.comp (read_cont b o i)

lemma palette_local (G : Gauge) (b : ℕ) (o : Site n) : LocalOn ↑(hull b o) (palette (G:=G) b o):= fun _ _ h=> funext fun i=> congr_arg G.curvature (reads_face b o i _ _ h)
lemma palette_gauge (t : Site n→G.El) (b : ℕ) (o : Site n) (U : Config G n): palette b o (gauge t U)=(fun i=>G.adjoint (t o) (palette b o U i)):= by
  funext i; unfold palette; simp only [Function.comp_apply,read_gauge, G.curvature_conjugate]

lemma healthy_palette {τ:ℝ} (hτ : 0 ≤ τ) (h : 2*(b+1)<n.val) {U : Config G n} (hu : Healthy τ (hull b o) U):
     ‖palette b o U‖ ≤ τ:= (pi_norm_le_iff_of_nonneg hτ).mpr fun i=> (G.curvature_norm _).trans (chords b U τ hu h i)

def horizon (i : ℕ):= 4*i

/-- Link chart on Room, padding with exact zero, as a function of palette
coords. Requires fitting to read. -/
def pane (o : Site n) (h : 2*(b+1)<n.val) (v : Palette G b) : Directions G n:= fun i=>
    if e : i∈ Room o b then record (word G h ⟨i,e⟩) v else 0

variable (h : 2*(b+1)<n.val)

@[simp] lemma pane_blank (G : Gauge) (o : Site n) : pane (G:=G) o h 0=0:= by
  funext i; unfold pane; split
  · unfold record; rw [stream_blank,G.mat_one,G.plog_one]; rfl
  rfl

def scaled (Q : Bath G k) (b : ℕ) (τ : ℝ) := Q.price^2*horizon b*τ
def sway (Q : Bath G k) (b : ℕ): ℝ := span Q (horizon b)
structure Safeguard (Q : Bath G k) (b : ℕ) (τ : ℝ) : Prop where
  threshold : 0 ≤ τ
  ready : τ≤Q.tile
  outer : horizon b*(Q.price*τ) ≤ Q.tile

lemma porch (Q : Bath G k) (o : Site n) {τ : ℝ} (v : Palette G b)
    (hw : Safeguard Q b τ) (ht : ‖v‖ ≤ τ):
    Bill k (bolt Q) (sway Q b) (pane o h) v ∧ ‖pane o h v‖ ≤ scaled Q b τ := by
  let Z i := fun x : Palette G b=> pane o h x i
  have hm i : Bill k (bolt Q) (sway Q b) (Z i) v ∧ ‖Z i v‖ ≤ scaled Q b τ := by
    unfold Z pane; split
    next he=>
      obtain ⟨e,h₁,-⟩:= posed Q v hw.ready ht (horizon b) (word G h (⟨i,he⟩:Dim o b)) (lengths_word ..) hw.outer
      exact ⟨e,h₁⟩
    have hs:=hw.threshold
    exact ⟨(fixed 0 k v (zero_le_one.trans (span_one_le Q (horizon b)))).up (zero_le_one.trans (span_one_le Q _))
      (by rw [norm_zero]; exact zero_le_one.trans (bolt_pos Q)),by simp only [norm_zero]; unfold scaled; positivity⟩
  have ht' := hw.threshold
  exact ⟨Bill.bundle (zero_le_one.trans (bolt_pos ..)) (zero_le_one.trans (span_one_le ..)) fun i=> (hm i).1,
    (pi_norm_le_iff_of_nonneg (by unfold scaled; positivity)).mpr fun i=>(hm i).2⟩

/-- Exact equality conditions. First pay individual letter recovery,
then require recoverability of each entire link at which the payload
will use plog. This is a multi-scale condition when used for changing another
set of paths. -/
lemma binds (Q : Bath G k) (o : Site n) (U : Config G n)
    (hp : ∀ i : Turn b, G.chord (registered b U o i) ≤ Q.tile)
    (hz : ∀ i : Dim o b, G.chord (spine U o i.val) ≤ Q.tile):
    Agrees ↑(hull b o) (spine U o) (increment 1 (pane o h (palette b o U))) := by
  intro i hi hi'
  let I:Dim o b:=⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hi'⟩⟩
  dsimp only [increment,pane]; rw [dif_pos (show i ∈ Room o b from I.property),record,palette,enacted Q _ _ (fun i _ => hp _)]
  change spine U o I.val=G.lieExp (G.plog (G.mat (Next.Rank.Spindle.played (registered b U o) (word G h I))))*1
  rw [← spun,mul_one,Q.true _ (hz _)]

/-- Equality at the physical tested budget point (weak inequalities ok). -/
lemma enters (Q : Bath G k) (o : Site n) {τ : ℝ} (U: Config G n)
    (hp : ∀ i : Turn b, G.chord (registered b U o i) ≤ τ) (hs : Safeguard Q b τ):
    Agrees ↑(hull b o) (spine U o) (increment 1 (pane o h (palette b o U))) := by
  refine binds h Q o U (fun i=> (hp i).trans hs.ready) fun i=>?_
  rw [spun U o h i]
  have hv: ((List.length (word G h i)):ℝ) ≤ horizon b:= by exact_mod_cast lengths_word ..
  exact ((played_cost _ (registered b U o) hs.threshold hp).1).trans ((mul_le_mul hv (le_mul_of_one_le_left hs.threshold Q.extra) hs.threshold (Nat.cast_nonneg _)).trans hs.outer)

variable (hL : LocalOn ↑X F) (hX : X⊆ hull b o) (hF : GaugeInvariant F)
include hL hX hF
 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Germ valid for every configuration within the *strict* chord
criteria, even if it does not preserve the flag. Covers masks boundaries
by using spare strict slack in the uniformity gates. -/
lemma carried (Q : Bath G k) (U : Config G n)
    (he : ∀ i : Turn b,G.chord (registered b U o i) < Q.tile)
    (hz : ∀ i : Dim o b,G.chord (spine U o i.val) < Q.tile):
    F =ᶠ[𝓝 U] (F ∘ increment 1 ∘ pane o h ∘ palette b o):= by
  have hp (i : Turn b): ∀ᶠ W in 𝓝 U, G.chord (registered b W o i) ≤ Q.tile := (G.continuous_chord.comp (read_cont b o i)).continuousAt.eventually
    (ge_mem_nhds (he i))
  have ht (i:Dim o b): ∀ᶠ W in 𝓝 U, G.chord (spine W o i.val) ≤ Q.tile := (G.continuous_chord.comp
    (show Continuous (fun W:Config G n=>spine W o i.val) by unfold spine Lattice.gauge fingers leaves expandAt; fun_prop)).continuousAt.eventually
    (ge_mem_nhds (hz i))
  filter_upwards [eventually_all.mpr hp,eventually_all.mpr ht] with W hp ht
  exact (hF (fingers W o) W).symm.trans (hL _ _ (agrees_mono (binds h Q o W hp ht) (fun _ u=> hX u)))

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma current (Q : Bath G k) {τ : ℝ} (hτ : 0 ≤ τ) (U : Config G n) (hu : Healthy τ (hull b o) U)
    (hp : τ < Q.tile) (hz : horizon b*(τ:ℝ) < Q.tile):
    F =ᶠ[𝓝 U] (F ∘ increment 1 ∘ pane o h ∘ palette b o):= by
  have he:=chords b U τ hu h
  refine carried h hL hX hF Q U (fun i=> (he i).trans_lt hp) fun i=>?_
  rw [spun U o h i]; have hD:= (played_cost (word G h i) (registered b U o) hτ he).1
  exact hD.trans_lt ((mul_le_mul_of_nonneg_right (show ((List.length (word G h i)):ℝ) ≤ horizon b by exact_mod_cast lengths_word ..) hτ).trans_lt hz)

omit hL hX hF in
/-- Composition cost via path changes for the payload as a function of
palette variables throughout the small ball. Preserve polynomial texture
powers for e.g. Taylor pricing in these variables. -/
lemma circulation (Q : Bath G k) {A d τ:ℝ} (hd : 0 ≤ d) (o : Site n)
    (hτ: Safeguard Q b τ) (hC : ∀ y : Directions G n, ‖y‖ ≤ scaled Q b τ → Bill k A d (F ∘ increment 1) y)
    (v : Palette G b) (hv : ‖v‖ ≤ τ):
    Bill k (cap k (bolt Q) A d) (sway Q b) (F ∘ increment 1 ∘ pane o h) v := by
  obtain ⟨e,hs⟩:=porch h Q _ v hτ hv
  exact e.comp (hC _ hs) hd (zero_le_one.trans (span_one_le Q _))

end YM.RG3.Pan
