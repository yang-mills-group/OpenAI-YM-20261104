import YM.X.Bend.Wider
import YM.X.Dock.Affair
import YM.X.Stage.P1
/-!
# T on X₁. CP5.

Position scheme of P1, CP5 adds genuine inversion of T/c_T on SAME normalized
independent Wilson regulator array, proving nonzero invariant detector, unit
limiting tangent, formal transform back and the calibrated predictions at horizon
d and each arity, through order ONE. It's coefficientwise formal but **only**
asserts existence of continuum limit on each separated joint profile (at present
support and FO bounds proven separately; no power rate in R cutoff used!), of
renormalized correlations orders zero & ONE. Does not assert actual continuum
positive-order matching, at any order > zero. Mass-independent N, scale flows,
β, OPE stuff all NOT part of this result.

T reconstruction: seven entries of Board7 give smeared on smooth product
SO(4)-invariant profiles, compact separation >4, labels in `menu` and `mainT`
 precisely b/U/U as in manuscript, theta not read on shifted g-exact physics. rankT
 is the connected moment (because test is factored; take conn of the profile
 array, so finite regulator uses lower order diagrams with same center convention
 on those lower profiles). Bolt in trians is the canonical integration by parts
 formula for the single curled ∂ distribution; cp uses Lean Rel.Eval calculus
 in real functions (verified even integrates for all masks on stipulated profiles,
 extends Green by its weak derivative = classical as local L¹-pairings by
 Dock.green_weak). sumI uses un-normalized mode coefficients inside ∗ tracker ∗,
 then overall, which summes the contraction p*E^-*M*M
 (see Affair mF, pF / bridge_angle), restoring (sqrt(2)^-1)^5 for normalized
 tensor legs. Thus CP5 identifies COEFFICIENT value precisely eq.(trians) norm
 with negative pairing. Route is via native-period Stokes/chiral estimate, not
 comparing all of lattice X scheme to continuum L² perturb counterterms. Only
 this coefficient continuum tensor expression made. (No theory of distributions
 needed; definition is by IBP using functions and every integral justified.)
 Parity uses latms sign tensor (-1)^slots. Pole∆Vol argument.

lean axiom audits attached subset. Always use same F.Shop. Also use ANYK at same
 regulator q>1. need compare θ k^d continuation beyond order one.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Pert Pert.Position Maxwell Maxwell.Free Function Filter Set Jet Detector Ribbon
open scoped Topology Classical BigOperators
variable {G:Gauge} (h:G.Simple)
open Bend MeasureTheory
structure Knocker {F:Labels.Frames G}{c:ℝ}(T:Booth c F)(q:ℕ+)(hq:1<q.val)(K:Bare.Shop F): Prop where
   early : MeshOne h q hq K
   legitimate : BeaconTest K hq h T
   definedA : ∀ᶠ k:ℕ in atTop, Genuine (curveF K q h T k)
   holdsA : Tendsto (fun k=>curveF K q h T k 1) atTop (𝓝 1)
   eigen (B:Pert.Position.Buffer F 6) : HasDerivAt (fun t:ℝ=>wants T.r1 (market F (t•B) (pureBank F 6))) 0 0
   reset : ∀ᶠ k in atTop, metricT T (renormal K q h T k 6)= headway
   retained d : ∀ᶠ k in atTop,(nested F h K d).D ∘ (renormal K q h T k d)=just ((nested F h K d).D (pureBank F d))
   tensorP d : ∀ᶠ k in atTop, pulls (par F d) ∘ (renormal K q h T k d)= turn (renormal K q h T k d)
   evaluated : let a:=mainT c T.r1; ∃ (r R:ℝ)(χ:Haze.Floor R), R<r ∧ Pulse.Curve a⊆ Pulse.Region 3 r ∧ Integrable (fun x:Points 3=> a x*(↑(trians G χ (x 0) (x 1) (x 2)):ℂ)) ∧ a.applyTo (fun x=>↑(trians G χ (x 0) (x 1) (x 2))) = ↑T.normalC
   crown d (v:Section F d) : Tendsto (fun k=> lookie F v (renormal K q h T k d 1)) atTop (𝓝 (lookie F v (firstX K q hq h d)))
lemma lit {F:Labels.Frames G}{c:ℝ}(T:Booth c F)(q:ℕ+)(hq:1<q.val)(K:Bare.Shop F)(hw: BeaconTest K hq h T): Knocker h T q hq K:= by
   refine ⟨green h K q hq,hw,well K q h T hq hw, cert K q h T hq hw, fun B=> slipped T.r1 K hq h B, canonical K q h T hq hw, θ_report K q h T hq, fun d=> θ_par K q h T hq hw,?_,fun _=> crown_endpoint K q h T hq hw⟩; let a:= mainT c T.r1; obtain ⟨r,hr,ht,hp⟩:= prepare_v K h a; obtain ⟨χ⟩:=Haze.Floor.make (R:=r/2) (by linarith); have hu:r/2< r:= by linarith
   obtain ⟨he,hy⟩:=targetT χ hq K h hu a hp ht; exact ⟨r,r/2,χ,hu,ht,he,hy.symm.trans hw⟩
-- endpoint (extension partial)
theorem coupling_lit {p:ℝ}(hp:0<p)(f:Extraction.Order):∃ (C:Family G)(g:Extraction.Order) (S:Table C.book)(A:PertExtension.Actual C (f.refine g) S), C.Makes ∧ C.path.levels.clock.kernel.penalty=p∧ ∃ (K:Bare.Shop C.labels)(c:ℝ)(T:Booth c C.labels), K.H=C.params∧K.S=C.localSection ∧ ∀ (q:ℕ+)(hq:1<q.val), Knocker h T q hq K := by obtain ⟨C,g,S,A,hA,hB,K,kH,kS,hW⟩:= coherence_one h hp f; obtain ⟨c,T,hx⟩:= can_booth K h; exact ⟨C,g,S,A,hA,hB,K,c,T,kH,kS,fun q hq=> lit h T q hq K (hx q hq).2⟩
end YM.PositionX
