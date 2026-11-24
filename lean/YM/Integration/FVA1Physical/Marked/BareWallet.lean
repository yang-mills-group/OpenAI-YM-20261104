import YM.Integration.FVA1Physical.Marked.WalletSplit
import YM.MergeProof.Pitch

/-! At initialization one may activate only single physical sources.
The actual masked wallet then agrees on every healthy source stencil with
the whole independent square-free insertion product, including all mixed
coefficients. Failed singletons retain the explicit physical mask. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Multi Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset
open MergeProof.Accent Extra.Trajectories
open scoped Classical BigOperators
variable {V Ω : Type} [Fintype V] [DecidableEq V] {B : Census V} {G : Gauge} {c : Side}
    {b d : ℕ} {ξ : V→ℕ} {o : V→Site c} {P : Rep G c} (W : Rooms.Wallet Ω o P B ξ d b)
    (t : Ω) (cut : ℕ) (g : ℝ)
local notation "A" => Stanza.son (W.prediction t) b

/-- The unmasked, short single-source reading in the actual bare program. -/
def bareLeaf (j : V) (v : Config G c) : ℝ :=
    W.weight t (Hot.one B j) * (A).wake (Hot.one B j) ((A).short (W.activation t) cut) o g v

/-- Explicit closed formula for the full log on any field. When a source
fails its own mask, its whole single coefficient is absent. Mixed coefficients
of the density are computed by the true square-free exponential. -/
theorem singleton_render (isolated : ∀ s : Senses B, 2 ≤ (essence s).card → W.weight t s=0)
    (v : Config G c) :
    W.render cut g t v =
      Mach B (fun j=> if Healthy P.p.threshold (Tale.court P.p.B (o j)) v then
        ((bareLeaf W t cut g j v : ℝ):ℂ) else 0) := by
  apply Marker.Poly.ext
  intro s
  by_cases single : s.val.card=1
  · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp single
    have eq : s=B.fire j := Subtype.ext hj
    subst s
    rw [sing]
    have root : Sonnet.root (Hot.one B j)=j := Finset.mem_singleton.mp (Classical.choose_spec (Hot.one B j).property)
    rw [show (W.render cut g t v).part (B.fire j) = _ from W.only (Hot.one B j) cut g t v]
    change ((W.weight t (Hot.one B j) * masked P.p.threshold
      (Tale.court P.p.B (o (Sonnet.root (Hot.one B j))))
      ((A).wake (Hot.one B j) ((A).short (W.activation t) cut) o g) v : ℝ) : ℂ) = _
    rw [root]
    by_cases hv : Healthy P.p.threshold (Tale.court P.p.B (o j)) v
    · rw [if_pos hv, masked_eq _ _ _ _ hv]; rfl
    · rw [if_neg hv, masked_ne _ _ _ _ hv, mul_zero,Complex.ofReal_zero]
  · by_cases maxed : s=B.quiet
    · subst s; rw [W.quiet,mute]
    have nz : 0<s.val.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      (fun e=>maxed (Subtype.ext e)))
    have many : 2 ≤ s.val.card := by omega
    let s' : Senses B := ⟨s,Finset.card_pos.mp nz⟩
    have wt : W.weight t s'=0 := isolated s' many
    rw [hush _ s many,show (W.render cut g t v).part s = _ from W.only s' cut g t v]
    change ((W.weight t s' * _ : ℝ) : ℂ)=0
    rw [wt,zero_mul,Complex.ofReal_zero]

/-- The sole comparison at each physical bare source is before its mask.
No independent mixed coefficients, cumulants or density hypothesis is needed. -/
theorem healthy_source_product
    (isolated : ∀ s : Senses B, 2 ≤ (essence s).card → W.weight t s=0)
    (F : V → Config G c → ℂ) (v : Config G c)
    (healthy : ∀ j, Healthy P.p.threshold (Tale.court P.p.B (o j)) v)
    (dictionary : ∀ j, ((bareLeaf W t cut g j v : ℝ):ℂ) = F j v) (s : B.Mode) :
    (Poly.pass (W.render cut g t v)).part s = ∏ j ∈ s.val, F j v := by
  rw [singleton_render W t cut g isolated]
  simp_rw [if_pos (healthy _),dictionary]
  exact pass_fire _ s
end YM.Integration.FVA1Physical.Marked
