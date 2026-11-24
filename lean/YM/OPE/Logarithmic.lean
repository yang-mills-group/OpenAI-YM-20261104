import YM.OPE.Mountains.Sampling
import YM.OPE.ElementaryLog
/-!
# All-horizon all-phase polylogarithmic factorization, from some matrix ticket

Public intermediate version. ***At this tier, NOT claiming the ticket is satisfied***.
Everything here is on the actual hierarchy of a constructed `Spec.Final`, and
we permit any calibration and compatible `Table` & derivatives already chosen
with `Facilities`. Pricing in the `MatrixTicket` from `Log/Measuring` is
additional: just a proposal for a sufficient, explicit further hypothesis,
not obtained in the lemmas here. It only concerns *one-field* norm bounds.
From it we get the full logarithmic powers, including single-scale for direct
readout and the `grace` factors, and the uniform over all ratios permitted by
`Convoy` estimates. `Arboreal.prestige` is the ∏ of log costs
(1 + log(1/root scale)) and (1+log(1/scale at internal vertex)) for nonroot
ones. No subpower remainders needed or offered in these prices. Every given
finite tree of the `AllShapes` results and every fixed configuration scope
in `LogError` admitted; joint over the full range of degenerating ratios (no
successive limits in them). Trees don't change the `ope`! See also
`Mountains/Assembly` for even partial (open vertex) sign estimates.
`prepared` gives realizing witnesses of Final & Schedule(facilities) & P
satisfying all the older subpower version withouts. They work approaching the
extension here; don't change convention for it. Tests and consumers can retain
all those estimates, and don't require this conditional ticket for their use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Finset Real Log Arboreal Arboreal.Mountain
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge} {C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)

/-- All-scale logarithmic Shape extension. Exact joint authority includes
    all-price upper powers (may use one common for any finite list of verdicts). -/
structure LogTrace (P:Prescription U.sector.derivatives) : Prop extends SingleLog U P where
    tickets {I:Type}[Fintype I] (s:Arboreal I)(v:I→ C.book.Token)(w:Mode U.sector.derivatives)(D:I→ ℕ)(M δ:ℝ):
       0 ≤ M → 0 < δ → ∃ p:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(t:I→ℝ), t s.root=r → s.Convoy M δ t x → ∀ k:ℕ,p ≤ k → LogRate U s P w v D x t k
    testing {I J:Type}[Fintype I][Fintype J](s:Arboreal I)(v:I→ C.book.Token)(q:J→ C.book.Token)(n:ℕ)(M δ c:ℝ):
       0 ≤ M → 0 < δ → 0 < c → ∃ p:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(t:I→ℝ)(y:J→E4), t s.root=r→ s.Convoy M δ t x → ClearOf (x s.root) y c→ ∀ k:ℕ,p≤k → LogError U s P v q n x t y k

lemma tickets_suffice (L:Facilities C F S) {φ:Filter (ℕ×ℕ)}[φ.NeBot] (hp:φ ≤ F.fuse)
    (V:MatrixTicket (C:=C) S U.sector.derivatives φ){P:Prescription U.sector.derivatives}(hP:P.Coherent): LogTrace U P:= by
    have he:= first_log U L hp V hP; obtain ⟨W,r,D,c⟩:= L.costlier; exact ⟨he,fun s v w d M δ hm he=> Mountain.pricing U hP L.toServices hp c V v d w hm he s, fun s v q n M δ c' hm he=> Mountain.pricing_error U hP L.toServices hp c V v q n hm he s⟩ -- namespace? use full

theorem conditional {G:Gauge}(h:G.Simple){b:ℝ}(hb:0<b)(F:Extraction.Order) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ ∃ (g:Extraction.Order)(S:Table C.book), Facilities C (F.refine g) S ∧ ∃ (U:Spec.Final C (F.refine g) S) (P: Prescription U.sector.derivatives), AllShapes U P∧ (∀ (φ:Filter (ℕ×ℕ)) [φ.NeBot], φ ≤ (F.refine g).fuse→ MatrixTicket (C:=C) S U.sector.derivatives φ → LogTrace U P):=by
    obtain ⟨C,hB,g,S,hV,U,P,hP⟩:= prepared G h hb F; exact ⟨C,hB,g,S,hV,U,P,hP,fun φ _ hf V=> tickets_suffice U hV hf V hP.coherent⟩
end YM.OPE
