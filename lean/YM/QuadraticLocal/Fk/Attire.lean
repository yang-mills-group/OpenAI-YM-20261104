import YM.QuadraticLocal.Fk.Vesper
import YM.Comparison.RG02.Integral.Model
import YM.AllOrder.Floe.Circle
/-!
# Current vacuum action presentation to the unmasked operator

No mask-removal claim on actual. This connects WHOLE intended action (all fluctuation
 orders in given high assignment) to the `Fk` prescription, at all its calculations;
 use with `Q0.program`: for authenticated epochs this `Layout` is exactly the model
 used, not post-step compare datum inserted in place of the action. Note the overall
 sign: Floe talks about POSITIVE `mainTerm`, including loop part in the same sign,
 and supplementary terms; `Score` uses exponent of its NEGATIVE
 with indicated prefactor. This file only addresses the ACTION on Link (before block).
 Haar and tree factors in `Dress` not additional action on the gauge links.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Faith
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Extra.Iteration
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet AllOrder.Floe
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{n : Side}
namespace Costume
open AllOrder.Floe Pace
variable (R:PathData G) (p:Clip) (F:Finset Age) (u:Floe.Layout G)

-- expansion without reset.. choose exponent sign separately below
abbrev basic (u:Floe.Layout G): Scene G:= grouping 0 u F p R
local notation "u*"=> ( grouping 0 u F p R )
local notation "Φ"=> (Stationary.Link G n)
lemma accountant : basic R p F u= ( Pace.base p R + AllOrder.Haiku.Coat.clerk (fun _=>Precision.loop R) 0 + ∑ i∈F, Haiku.Coat.trade i.e (u i) ):=by
 funext k n; unfold basic Pace.grouping; simp only [Pace.shiftB,Pi.add_apply,Pace.glory,Finset.sum_apply,Pace.moiety,Crest.gone,Crest.nogo,add_zero,Crest.nostep] -- notation check

-- Actual polynomial-germ coefficients.Accounts from Operator.Packet.Power Mark auxiliaries set via `grant`
local notation "F₀"=> ( Stationary.input G n )

variable (A: Stationary.Link G n) {a C Λ:ℝ} (h:Floe.Legal F u) (hR:R.Bounds p a C Λ)
variable (K:ℕ)
include h
lemma charge_jet (i:Age) (hi:i∈F): Haiku.Coat.trade i.e (u i) K n A=Radial.jet (fun z:ℝ×Stationary.Link G n=>Floe.sketch u i n z.1 (F₀ z.2)) (K+2) (1,A):= by
 obtain ⟨b,C',hb,hc⟩:= h.rent i hi; let w:Stationary.Link G n→ℝ:= turnSeries (u i); have hw:AnalyticAt ℝ w 0:= turns_analytic _ hb hc;
 have he: ∀k < i.r, iteratedFDeriv ℝ k w 0=0:= (rays_jet hw i.r).1 (turns_low _ hb hc); change _ = Radial.jet (fun z:ℝ×Stationary.Link G n=> z.1^i.stamp*w z.2) (K+2) (1,A); unfold trade; split; next hh=>
    rw [favor_exp w hw.contDiffAt, if_pos (show i.stamp≤K+2 by have ht:=i.recovery; omega),one_pow,one_mul,show K+2-i.stamp=K-i.e+i.r by have ht:=i.recovery; omega];
 next hh=> exact (favor_pocket w hw.contDiffAt (i.e+2) i.r i.stamp (K+2) he 1 A i.recovery (by omega)).symm
-- Pseudovacroster for Fk.Height.S.Models.Y.St culture. unit h.B tower.Frame.Clock.Weight
-- membership basis unscaled beta.in
local notation "H₀"=> (u*)
local notation "B₀"=> (Floe.audition (f:=n) R p u F)
def evaluation (z: ℝ×Stationary.Link G n) := (Floe.audition (f:=n) R p u F z.1 (Stationary.input G n z.2))
local notation "E"=> (evaluation (n:=n) R p F u)

include hR
lemma genuine : grouping 0 u F p R K n A= Radial.jet (evaluation R p F u) (K+2) (1,A):=by
 let f:Φ→ℝ:=mainTerm p R ∘ F₀; let g:Φ→ℝ:=Precision.loop R ∘ F₀; let T':=ℝ× (Stationary.Link G n); let f'(z:T'):= z.1^ (0:ℕ)* f z.2; let g'(z:T'):=z.1^ (2:ℕ)*g z.2; let Q i (z:T'):= z.1^(Age.stamp i)*turnSeries (u i) (m:=n) z.2; let W:= ∑ i∈F,Q i; have hz: E= f'+g'+W:= by
    funext x; unfold evaluation Floe.audition; simp only [Pi.add_apply,Finset.sum_apply, Floe.sketch,Pi.smul_apply,smul_eq_mul]; unfold W; simp only [Finset.sum_apply,f',pow_zero,one_mul,Laplace.primitive]; rfl
 change basic R p F u K n A=_; rw [accountant]; have hf: ContDiffAt ℝ ω f 0:= (Pace.intent_point p R hR n).analytic.contDiffAt; have hg:ContDiffAt ℝ ω g 0:= (turns_analytic (R.loop) hR.width hR.two).contDiffAt;
 have hb: ContDiffAt ℝ ω f' 0:=(contDiffAt_fst.pow _).mul (ContDiffAt.comp (f:=Prod.snd) (g:=f) (0:T') hf contDiffAt_snd); have hp:ContDiffAt ℝ ω g' 0:=(contDiffAt_fst.pow _).mul (ContDiffAt.comp (f:=Prod.snd) (g:=g) (0:T') hg contDiffAt_snd);
 have hQ i (hi:i∈F): ContDiffAt ℝ ω (Q i) 0:= by obtain ⟨b,C,hb,hc⟩:= h.rent i hi; exact (contDiffAt_fst.pow _).mul ((turns_analytic (m:=n) (u i) hb hc|>.contDiffAt).comp (f:=Prod.snd) (0:T') contDiffAt_snd)
 have hw : ContDiffAt ℝ ω W 0:= by rw [show W = fun x=> ∑ i∈F,Q i x from funext fun p=> Finset.sum_apply ..]; exact ContDiffAt.sum hQ
 rw [hz,jet_add (show ContDiffAt ℝ ω (f'+g') 0 from hb.add hp) hw _,jet_add hb hp]; simp only [Pi.add_apply,Finset.sum_apply]; unfold W; rw [Floe.goth hQ]; congr 1
 · unfold f' g'; change Radial.jet f (K+2) A + Radial.jet g K A = _; rw [favor_exp f hf,favor_exp g hg,if_pos (Nat.zero_le _),if_pos (show 2 ≤ K+2 by omega),one_pow,one_pow,one_mul,one_mul,Nat.sub_zero,Nat.add_sub_cancel]
 exact Finset.sum_congr rfl (fun i hi=> Costume.charge_jet F u A h K i hi)
-- native Φ.Price.F attendant. Holds weight at every g ≠0. Unmasked; use TRUE stencil clipping when actually charging budgets; this formula doesn't address that.
omit hR h
open Marker Multi
open Comparison.RG02
variable {V:Type}[DecidableEq V]{D:Census V} (Y:Bulk.Colors D G n)
lemma native (g:ℝ)(he:g≠0) (C:ℝ) (U:Config G n): Integral.weight g C U (QuadraticLocal.Fk.grant u F Y) p R=Real.exp (C-Integral.temperature g* ( Floe.audition R p u F (f:=n) g U )):=by
 unfold Integral.weight Integral.localClassic; change Real.exp (C- _ - loop R U)=_; unfold Floe.audition Laplace.primitive Integral.temperature; simp only [Pi.add_apply, QuadraticLocal.Fk.grant, QuadraticLocal.Fk.money]; apply congr_arg; field_simp; ring
end Costume
end YM.QuadraticLocal.Faith
