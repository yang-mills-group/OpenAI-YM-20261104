import YM.RemainderComparison.Arms
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-!
# Actual denominators and insertion derivative bounds

The estimate immediately before quotient/cumulant use, on one real step of the ACTUAL C.
Works at every output, including configurations with arbitrary flagged sets; left derivative
order arbitrary finite `j` (uses no point-dependent closeness assumption). For example, a mask
on the *integration* field at the fine scale can be imposed in `f₁` below without having to
keep track of its threshold in these derivatives. This does NOT say the resulting price of such
a numerator at zero differentiations (still relative to the denominator) is small.

`signed_step` quantifies over marker-coefficient space directly; use also one real or complex
coefficient at a time. There is no dimension-equivalence or cost implicit in that choice; the
pointwise integrated norm in the conclusion is the same norm. Implement any new nilpotent-algebra
norm as such or apply this bound before integrating/summing over arrivals. In particular,
never normalize against a merely assumed unit mass in the fine variable.

For applications to vacuum scalar alignments use `Germ` plus support-restricted `supported_derivative`
with union of all changed links; numerator and denominator can use the very same window. No
change to ranked Frames. These estimates don't sum over supports.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Relative
open Function Filter Finset Lattice RG Wilson MeasureTheory Push Push.Uniform
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat WardBin.Lies
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}

-- Analysis constants only depend on G and finite demand.
structure Sensors (G : Gauge) (j : ℕ) where
  m : ℝ
  geometry : PaintSupply G j m
  e : ℝ
  i : ℝ
  l : ℝ
  exp : Brush j e 1 Real.exp 0
  inv : Brush j i 1 (fun x : ℝ => x⁻¹) 1
  log : Brush j l 1 Real.log 1

lemma brush_bound (j : ℕ) {x : ℝ} {f : ℝ → ℝ} (h : ContDiffAt ℝ (↑j) f x) :
    ∃ k : ℝ, Brush j k 1 f x := by
  let k := ∑ i∈range (j+1), normJ i f x
  refine ⟨k,Brush.offer.2 ⟨h,?_⟩⟩
  exact fun i hi=>single_le_sum (f:=fun i=>normJ i f x) (fun _ _=> norm_nonneg _) (show i ∈ range (j+1) from mem_range.mpr (by omega))

def fieldSensors (G : Gauge) (j : ℕ) : Sensors G j := Classical.choice <| by
  obtain ⟨m,hM⟩ := paint_supply G j
  obtain ⟨e,he⟩ := brush_bound j (x:=0) Real.contDiff_exp.contDiffAt
  obtain ⟨i,hi⟩ := brush_bound j (show ContDiffAt ℝ (↑j) (fun x : ℝ => x⁻¹) 1 from (contDiffAt_id (𝕜:=ℝ) (x:=(1:ℝ))).inv one_ne_zero)
  obtain ⟨l,hl⟩ := brush_bound j (x:=1) (Real.contDiffAt_log.mpr one_ne_zero)
  exact ⟨⟨m,hM,e,i,l,he,hi,hl⟩⟩

variable {j N m q : ℕ}

def jetCost (P : Sensors G j) (K : KernelChoices) (β : ℝ) (ℓ n : ℕ) : ℝ :=
  score G K β n j (paintCost G ℓ j P.m) P.e
lemma scene_univ (V : Config G c) (l : ℕ) : edgeScene l V univ = chug l V :=
  funext fun i=> by unfold edgeScene; rw [comp_apply, tap_univ]

lemma germ_scene {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Config G c → Y) (V : Config G c) {r v : ℝ}
    (h : Brush j r v (f ∘ edgeScene 1 V univ) 0) : Germ j f V := by
  let L : Directions G c →L[ℝ] Slab G c 1 :=
    ContinuousLinearMap.pi fun _=> ContinuousLinearMap.id _ _
  have hp : ContDiffAt ℝ j (f ∘ chug 1 V) (L 0):= by rw [map_zero,←scene_univ]; exact h.smooth
  exact hp.comp 0 L.contDiff.contDiffAt

section actual
variable (C : Family G) (hC : C.Makes) (hn : m < N)
    (P : Sensors G j) (V : Config G (C.side m q))
    (o : Finset (Edge (Site (C.side m q))))
local notation "κ" => C.path.levels.clock.kernel
local notation "S" => (C.path.levels.clock.op m q)
local notation "β" => (C.path.β N q (m+1))
local notation "Df" => (Rep.eval (C.path.rep N q (m+1)))
local notation "Q" => (StepData.push S (β) (Df))
local notation "W" => (jetCost P κ (β))

include hC hn
lemma window_step (l : ℕ) : (let d:= Q V; let f:=edgeScene l V o
    0 < d ∧ d=(C.path.rep N q m).eval V ∧ Brush j (W l o.card*d) 1 ((Q) ∘ f) 0 ∧
    Brush j (Lantern.clump j (W l o.card) P.l) 1 (fun y=> Real.log (Q (f y)) - Real.log d) 0) := by
  intro d f
  have hb:=hC.wilson
  have ht := (hb.steps N q m hn).1
  have hz := SectorNext.Vacuum.strictly C.path hb N q m hn.le V
  have hf : f 0=V:= edgeScene_center l V
  have hp : 0<Q V := by rw [← ht]; exact hz
  have hB : 0<Q (f 0):= hf.symm ▸ hp -- need beware dependent rewriting
  let y:=(C.path.rep N q (m+1)); have h:= y.envelope (hb.represents N q _ hn).good
  have he := root S β Df (fun i=> (SectorNext.Vacuum.strictly C.path hb _ _ _ hn i).le) (h.integrable _) h.meas.stronglyMeasurable
      (C.path.levels.transition_mass ..) (edge_window j V o l P.geometry) P.exp
  have hk := log_pivot S β Df (fun i=> (SectorNext.Vacuum.strictly C.path hb _ _ _ hn i).le) (h.integrable _) h.meas.stronglyMeasurable
      (C.path.levels.transition_mass ..) (edge_window j V o l P.geometry) P.exp hB P.log
  simp only [edgeScene_center] at he hk
  exact ⟨hp,(congr_fun ht V).symm,he,hk⟩

lemma signed_step {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (l : ℕ) (F : Config G (C.side (m+1) q) → Y) (hF : Integrable F (prior G _)) (hM : StronglyMeasurable F) :
    let d:= Q V; let f:=edgeScene l V o; let k:= W l o.card
    Brush j (Lantern.clump j k P.i*(d⁻¹*(k*(S).push β (fun i=> ‖F i‖) V))) 2
      (fun y=> (Q (f y))⁻¹ • (S).push β F (f y)) 0 := by
  intro d f k
  have he := window_step C hC hn P V o l
  have hp := Rep.envelope (C.path.rep N q (m+1)) (hC.wilson.represents N q _ hn).good
  have h : Q (f 0)= d:= congr_arg (Q) (edgeScene_center l V)
  have hz := divide S β (Df) (fun i=> (SectorNext.Vacuum.strictly C.path hC.wilson _ _ _ hn i).le) (hp.integrable _) hp.meas.stronglyMeasurable
      (C.path.levels.transition_mass ..) (edge_window j V o l P.geometry) P.exp (lt_of_lt_of_le he.1 h.ge) F hF hM P.inv
  simp only [edgeScene_center] at hz
  exact hz

-- In particular all left derivatives below are genuine even on mask seams.
lemma step_smooth : Germ j (Q) V := germ_scene _ _ ((window_step C hC hn (fieldSensors G j) V univ 1).2.2.1)
lemma log_smooth : Germ j (fun Y=> Real.log (Q Y)-Real.log (Q V)) V :=
  germ_scene _ _ ((window_step C hC hn (fieldSensors G j) V univ 1).2.2.2)
lemma signed_smooth {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : Config G (C.side (m+1) q) → Y) (hF : Integrable F (prior G _)) (hM : StronglyMeasurable F) :
    Germ j (fun V=> (Q V)⁻¹ • (S).push β F V) V :=
  germ_scene _ _ (signed_step C hC hn (fieldSensors G j) V univ 1 F hF hM)

lemma step_arm {l : ℕ} (hl : l≤j) (A : Slab G (C.side m q) l) (hr : ∀ e ∉ o, ∀ i, A i e = 0) :
    ‖leftDerivs (Q) (List.ofFn A) V‖ ≤ W l o.card * Q V * ∏ i, ‖A i‖ := by
  have H := (window_step C hC hn P V o l).2.2.1
  have h := (window_step C hC hn P V univ l).2.2.1
  have hs : ContDiffAt ℝ l ((Q) ∘ chug l V) 0:= by rw [← scene_univ]; exact (h.smaller hl).smooth
  simpa only [one_pow,mul_one] using supported_derivative j V o A hr hs H hl

lemma log_arm {l : ℕ} (hl : l ≤ j) (A : Slab G (C.side m q) l) (hr : ∀ e ∉ o, ∀ i, A i e = 0) :
    ‖leftDerivs (fun Y=> Real.log (Q Y)-Real.log (Q V)) (List.ofFn A) V‖ ≤ Lantern.clump j (W l o.card) P.l *∏ i, ‖A i‖ := by
  let f Y:= Real.log (Q Y)-Real.log (Q V)
  have H := (window_step C hC hn P V o l).2.2.2
  have h := (window_step C hC hn P V univ l).2.2.2
  have hs : ContDiffAt ℝ l (f ∘ chug l V) 0:= by rw [← scene_univ]; exact (h.smaller hl).smooth
  simpa only [one_pow,mul_one] using supported_derivative j V o A hr hs H hl

lemma signed_arm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {l : ℕ} (hl : l ≤ j) (A : Slab G (C.side m q) l) (hr : ∀ e ∉ o, ∀ i, A i e = 0)
    (F : Config G (C.side (m+1) q) → Y) (hF : Integrable F (prior G _)) (hM : StronglyMeasurable F) :
    let f V:= (Q V)⁻¹ • (S).push β F V; let k:= W l o.card
    ‖leftDerivs f (List.ofFn A) V‖ ≤ Lantern.clump j k P.i*((Q V)⁻¹*(k*(S).push β (‖F ·‖) V))*2^l* ∏ i, ‖A i‖ := by
  intro f k
  have H: Brush j _ 2 (f ∘ edgeScene l V o) 0 := signed_step C hC hn P V o l F hF hM
  have h: Brush j _ 2 (f ∘ edgeScene l V univ) 0 := signed_step C hC hn P V univ l F hF hM
  have ht : ContDiffAt ℝ l (f ∘ chug l V) 0:= by rw [← scene_univ]; exact (h.smaller hl).smooth
  exact supported_derivative j V o A hr ht H hl
end actual
end YM.RemainderComparison.Relative
