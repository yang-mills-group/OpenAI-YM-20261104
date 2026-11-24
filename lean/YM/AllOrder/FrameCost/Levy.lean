import YM.AllOrder.FrameCost.Iterate
import YM.OPE.Levy.Phase

/-!
# Paying OPE Levy *in the leading frames of this construction*

`FirstExtension` is not used. Instantiate price service along any
vanishing strictly shrinking sequence, including an extracted bad sequence.
Also show inverse subpower rates, as in the unselected Levy
branch, on all such sequences. These implications are useful for every-phase
matching. Not the later polylog sharp OPE budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.FrameCost
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Leading Next.UVStress Maxwell Spin Push.FiniteDetection.Free OPE
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {n : ℕ} {d e : ℕ} (h : Aligned F g U)
local notation "free" => Bel C.book
set_option quotPrecheck false
local notation "L" => C.labels

def sample (U : ℝ → FamilyFrame S) (r : Zoom) : Scaling S :=
    ⟨fun k=> U (r.r k),fun _=>1,r.r,fun _=>one_pos,r.positive,r.shrinking,r.limits⟩
lemma sample_trail (r : Zoom) : Tendsto r.r atTop trail :=
    tendsto_nhdsWithin_iff.mpr ⟨r.limits,Eventually.of_forall r.positive⟩
include h
lemma anchorage (r : Zoom) : Levy.Anchored F.sector.derivatives r (isoPanel (sample U r)) :=
    fun _ _ he x φ hφ => (anchored h φ he hφ x).comp (sample_trail r)

-- optional inverse rate for later perturbative operations
lemma at_trail (d : ℕ) : ∃ c : ℝ, 0<c ∧ ∀ᶠ r in trail, ∀ p:(free).Field d,
    ‖p‖^2 ≤ c * ‖leave d (U r) r p (Levy.reflect (C:=C) d p)‖ := by
    obtain ⟨c,hc,hT⟩ := FrameCost.coercive d h
    refine ⟨c,hc,?_⟩; filter_upwards [show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin,
      FrameCost.clock_time.eventually hT] with r hr hx
    rwa [FrameCost.clock_inverse hr] at hx
lemma sample_inverse (ht : Services C f S) (x : S.Field d) (r : Zoom) :
    RateLE atTop (Levy.meter (sample U r)) (fun i=>(U (r.r i) d).symm x) (d:ℝ) := by
    let X := sample U r
    let T:= Levy.meter X
    have ha := Levy.fixed_pair F d X ht x (Levy.bar F d x)
    obtain ⟨c,hc,hK⟩:= at_trail h d
    have hf:=sample_trail r
    intro a hd; have hm:= Levy.meter_big X
    filter_upwards [ha (a+d) (by linarith), (RateLE.const c hm) (a-d) (by linarith),
      hf.eventually hK,hf.eventually (h.respects d)] with i h1 h2 h3 h4
    let u:= U (r.r i) d; let p:= u.symm x
    have hv : u (Levy.reflect d p) = Levy.bar F d x:= by
       unfold Levy.bar Levy.reflect; rw [h4.1,h4.2,LinearEquiv.apply_symm_apply]
    have hx:= h3 p; change _ ≤ c*‖Levy.pair d S (X.r i • detectors) (u p) (u (Levy.reflect d p))‖ at hx
    rw [hv, LinearEquiv.apply_symm_apply] at hx
    rw [Real.norm_eq_abs,abs_of_pos hc] at h2
    have he : Real.exp (a*T i)^2 = Real.exp ((a-d)*T i) * Real.exp ((a+d)*T i):= by
       rw [pow_two,← Real.exp_add,←Real.exp_add]; congr 1; ring
    have hh:= hx.trans (mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_pos _).le)
    exact le_of_pow_le_pow_left₀ (n:=2) (by decide) (Real.exp_pos _).le (hh.trans_eq he.symm)

/- Routine bad-sequence universalization for trail. `P` may quantify all
 shapes and phases; compact bounds are *uniform*. -/
omit h in
lemma of_sampling {P : ℝ → Prop} (H : ∀ X : Zoom, ∀ᶠ i in atTop, P (X.r i)) : ∀ᶠ r in trail, P r := by
   by_contra hx
   obtain ⟨s,hs,hS⟩ := Pilot.contradictionTrail P hx
   -- shrink to STRICT ly
   have ht : Tendsto (FrameCost.clock ∘ s) atTop atTop := FrameCost.clock_time.comp hs
   obtain ⟨u,hu,hL⟩ := strictMono_subseq_of_tendsto_atTop ht
   let Y := FrameCost.clock ∘ s
   have hA : StrictAnti (s ∘ u) := by
      intro i j hij
      have hh:= hL hij
      rw [Function.comp_apply,Function.comp_apply, ← FrameCost.clock_inverse (hS (u i)).1,
         ← FrameCost.clock_inverse (hS (u j)).1]
      exact Real.exp_lt_exp.mpr (neg_lt_neg hh)
   let X : Zoom:= ⟨s∘u,fun _=>(hS _).1,hA, hs.mono_right nhdsWithin_le_nhds |>.comp hu.tendsto_atTop⟩
   obtain ⟨i,hi⟩:= (H X).exists; exact (hS (u i)).2 hi

lemma aligned_inverse (ht : Services C f S) (x : S.Field d) :
    RateLE trail FrameCost.clock (fun r => (U r d).symm x) (d:ℝ) := by
    intro a hd
    exact of_sampling fun X => sample_inverse h ht x X a hd

end YM.AllOrder.FrameCost
