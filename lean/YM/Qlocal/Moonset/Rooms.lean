import YM.Qlocal.Moonset.Theater
/-!
The state for a repeated comparison. Does not include the coupling reset (which operates at
 transfer) nor silently introduce a new income/wallet on each call to get different β. Supports
 declared up front. Uses real analytic mark kernels through the prescribed order; tracking
 `Lease` in real-cost space concurrently. No complex extension assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset.Rooms
open Function Filter RG Lattice Wilson Tree Gauge
open Marker Multi Extra.Trajectories Finset RG3.Script.Picnic
open Integration Integration.LocalComparison Integration.RiderTastePresentation
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern
open Publishing Parabola Reckoner
open Quipu.Eluder.Incline.Bookworm
open scoped Topology BigOperators Classical ContDiff YM.Qlocal.Payload
variable {G:Gauge} {n:Side}{Ω V J:Type} [DecidableEq V] {B: Marker.Census V} {ξ: V→ℕ}{d b:ℕ}
    {o:V→Site n} {P:RG.Rep G n}
-- `ready` will also require authorization on every possible path & momentum estimate at *whole* stencil.
-- This state is per step alternative Covenant; it does not identify an external test with one of the mark coordinates (these may depend on that test). Birth selected externally.
structure Wallet (Ω:Type)(o:V→ Site n)(X:RG.Rep G n)(B:Marker.Census V)(ξ:V→ℕ)(d b:ℕ) where
 prediction : Ω→Stanza B G ξ d
 activation (x:Ω) : (Stanza.son (prediction x) b).Decision
 weight : Ω→ Senses B→ℝ
 other : Taste Ω o X B
namespace Wallet
variable [Fintype V]
variable (T:Wallet Ω o P B ξ d b)
noncomputable abbrev plan (x:Ω)(w:ℕ)(z:ℝ)(s:Senses B)(U:Config G n):ℂ:= Dialect.Patchwork.substantive z w (Stanza.son (T.prediction x) b) (T.activation x) P.p o s (T.weight x s) U
-- whole polynomial publish at Once. Model & residual, mask attached. Core pure support path auth for all fields.E_Back Check
noncomputable def render (w:ℕ)(z:ℝ)(x:Ω)(U:Config G n) : Poly B:= ∑ s:Senses B, Poly.send s.val (Wallet.plan T x w z s U)
noncomputable def density (w:ℕ)(z:ℝ)(x:Ω)(U:Config G n): Poly B := Poly.pass (render T w z x U)*(T.other.leaf x).density U
lemma only (s:Senses B)(W:ℕ)(z:ℝ)(x:Ω)(U:Config G n) : (render T W z x U).part s.val=plan T x W z s U:= by
 unfold render; rw [Poly.part_sum,Finset.sum_eq_single s,Poly.part_send,if_pos rfl]
 · exact fun t ht he=> by rw [Poly.part_send, if_neg (show s.val≠ _ from fun h=> he (Subtype.ext h.symm))]
 simp
lemma quiet (W:ℕ)(z:ℝ)(x:Ω)(U:Config G n) : (render T W z x U).part B.quiet=0:= by
 unfold render; rw [Poly.part_sum]; refine Finset.sum_eq_zero fun s _=>?_ ; rw [Poly.part_send, if_neg (show _ from fun h:B.quiet=s.val=> s.prop.ne_empty (congr_arg Subtype.val h.symm))]
-- Equating render and Scribe. used to get `Certified` exact for output density.
variable {Q: Ray B} (p:Rental Q) {a A:ℝ} {S:Scribe Ω J G n B}{s: V→Support n}
include p
lemma sells (h: S.Spend P.p Q a A)(hu:S.Proper P.p s)(ha:0 ≤ a)
    (W:ℕ)(z:ℝ)(hv:∀ x j U,(S.send P.p x U).part (j:Senses B).val= Wallet.plan T x W z j U) : Scribe.send S P.p=render T W z:= by
 funext x U; apply Marker.Poly.ext; intro i; by_cases hi:i=B.quiet; · rw [hi,quiet]; exact Scribe.calm_send h p hu ha x U
 let j:Senses B:=⟨i, Publishing.regular_ray_nonempty_ _ hi⟩; exact (hv x j U).trans (only T j W z x U).symm
-- bind to actual stochastic moment law for canonical Mark reader.P.Payload.Clock.Era
omit p
lemma held (L:Gauges.Lamp B Ω P o) (W:ℕ) (z:ℝ)
    (H:∀ x i V,(L.publication (fun x i=>↑(T.weight x i)) x V).part (i:Senses B).val= Wallet.plan T x W z i V): L.publication (fun x i=>↑(T.weight x i))= Wallet.render T W z := by
 funext x U; apply Marker.Poly.ext; intro i; by_cases hi:i=B.quiet; · rw [hi,quiet]; unfold Gauges.Lamp.publication; rw [Poly.part_sum]; refine Finset.sum_eq_zero fun j hj=>?_ ; unfold Gauges.Lamp.request; rw [Poly.part_send, if_neg (show _ from fun h:B.quiet=j.val=> j.prop.ne_empty (congr_arg Subtype.val h.symm))]
 let j:Senses B:=⟨i, Publishing.regular_ray_nonempty_ _ hi⟩; exact (H x j U).trans (only T j W z x U).symm
-- width h ordinary; Ψ before clock.B mut rotate Price Controller. Invoice Keeper.
structure Usable (O: V→ Support n)(q: Ray B) (a w δ:ℝ) : Prop where
    rental : Rental q
    optics (x:Ω) : (Stanza.son (T.prediction x) b).Allows a 1 -- fix horizon name b shadow
    starts :∀ (x:Ω) i, q (i:Senses B).val* |T.weight x i| ≤1
    terrain :∀ i,O i⊆ Calendars.Uplink.habitat n w (o i)
    support :∃ X:Set (ℕ×ℕ), RetainsDeclared X T.other O
    threshold : 0<δ ∧ δ ≤1
    ready : Peak P o T.other q P.p.supportExponent δ δ
-- for calls with a fixed coupling-power aperture or tighter proof-of-gap desired
-- operands in Step.State relation always choose EXACT whole Y layout and activations
end Wallet
end YM.Qlocal.Moonset.Rooms
