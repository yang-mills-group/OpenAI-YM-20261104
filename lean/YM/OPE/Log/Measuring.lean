import YM.OPE.Log.PricePlot
/-!
# The matrix hypothesis

Just two ONE-field (all cutoffs, before `Next.Phase.genuine`) estimates. Kept as
hypothesis of the next stronger-price tier. It would NOT suffice just to
bound the bare l1 cone product used in the previous tier by a weaker subpower
or exponential on log(r); the hypothesis here prices the quota on the actual
physical quotient for fixed degrees, uniformly as moving captures k tend to UV.
It allows boundary choices depending on k.

The prices include normalization of the engineering footing, as specified in `quota`
(it is measured in dimensionless coordinates of horizon d). Do not request an
inverse estimate on the literal offshell coordinates between an arbitrary number
of levels. Along the refinement that underwrites the receipt at fixed k, not assumed to
be realizable also as a successive period/volume limit, both inlets and outlets are
priced. This distinction is needed because the slips for a matched word can
also have refinements and can interact with this common filter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open Next.UVStress Extraction
open scoped Topology BigOperators
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ι:Type}{I:Type}[Fintype I] {l:Filter ι}{T:ι→ℝ}{a b:ℝ}
    {k m j:ι→ℕ} {t:ℕ}
variable {f:Extraction.Order}{S:Table C.book}{B:DiffPlan S}
local notation "Y" => C.path.levels
local notation "α"=> C.path.levels.S.a
/-- Receipt for k prices (log power version). Explicit conditional hypothesis,
NOT implied by the statements being quoted from the baseline build. -/
structure MatrixTicket (S:Table C.book)(B:DiffPlan S) (𝓕:Filter (ℕ×ℕ)) : Prop where
    inlet (d:ℕ)(x:C.label d) : ∃ p:ℕ, ∀ᶠ k:ℕ in atTop, ∃ (y:C.label d)(q:ℕ × ℕ→ C.label d),
       S.project d y = S.project d x ∧ Tendsto q 𝓕 (𝓝 y)∧ ∀ᶠ i in 𝓕, quota C d k i.1 i.2 (q i) ≤ C.path.levels.clock.hatBeta k^p
    outlet (d w:ℕ)(L:S.Field d →ₗ[ℂ] ℂ) (h:w≤d) : (∀ e:ℕ,∀ he:e<w, ∀ x:S.Field e, L (B.rise (he.le.trans h) x)=0)→
       ∃ p:ℕ, ∀ᶠ k in atTop, ∀ (u:Filter (ℕ×ℕ)) [u.NeBot], u≤𝓕 →
       ∀ (q:ℕ×ℕ→ C.label d)(x:C.label d)(z:ℝ), (∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q u (𝓝 x) → ‖L (S.project d x)‖ ≤ C.path.levels.clock.hatBeta k^p / C.S.a k^(d-w) * z
variable {𝓕:Filter (ℕ×ℕ)} [𝓕.NeBot]
variable (U:Spec.Final C f S) (hT:Tendsto T l atTop) {W r D} (L: LogPackage C W r D)(hG:G.Simple) (i₀:I) (v:I→ C.book.Token) {s:ι→ I→ Cover}
local notation "σ'"=> (sigma v)
variable (hr:𝓕≤f.fuse) (h:MatrixTicket (C:=C) S U.sector.derivatives 𝓕)
include h hr hT L i₀ hG
open scoped Classical
lemma for_plots (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hj: Height C.S l T j a)(hp:b<a) (hx:∀ᶠ i in l,m i+1<j i)(hM: ValueStamp l T (fun i=> C.S.a (j i)/C.S.a (m i)))(ht:∀ᶠ i in l, Plot C (k i) (m i) (j i) (s i)) :
    ∃ g o : ι→ℝ, ∃ Q:ι→ C.label t, ValueStamp l T g ∧ RateLE l T o (-((t+1/16:ℝ)*(a-b)-(σ':ℝ)*a)) ∧
        ∀ᶠ i in l, Dress (C:=C) 𝓕 S (k i) (m i) (j i) (o i) (g i * C.S.a (m i)^t/C.S.a (j i)^σ') v (s i) t (Q i):=by
    choose p hA using fun i=> h.inlet (v i).1 (v i).2; let A i s:= (Y).clock.hatBeta (j i)^p s; let d i:=(v i).1
    obtain ⟨g,o,hg,he,hp⟩:= cost_funding L hG i₀ hT A d t hk hm hj hp hx hM U.room.cutoff (fun i=> (betaStamp hT hj).pow hT (p i)) -- order
    let y(i):= g i*C.S.a (m i)^t/C.S.a (j i)^σ'; let q i (x:C.label t):= Dress (C:=C) 𝓕 S (k i) (m i) (j i) (o i) (y i) v (s i) t x
    let Q i:= if hh:∃ x,q i x then hh.choose else 0
    refine ⟨g,o,Q,hg,he,?_ ⟩
    filter_upwards [hp,ht,eventually_all.mpr (fun i=> hj.grows.eventually (hA i))] with i hp ht hA; choose y' H hp' hT hA using hA; have hh:∃ x,q i x:= price_plot_M U hp y' hr hT hp' hA ht; rw [show Q i = hh.choose from dif_pos hh]; exact hh.choose_spec
end YM.OPE.Log
