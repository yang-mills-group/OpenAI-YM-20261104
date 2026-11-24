import YM.X.Scheme.Nested
import YM.PertExtension.StampedActual
/-!
# `Y0` — nested finite-regulator operator definitions in the position scheme; pre-coupling reset.

Usable for any witness with SectionData pop. Produces results also on
  same Sec of an Actual which has Spec.Final.
`Pay` packages one lower-stage analytic input: positive-order at **finite**
regulator real smooth frame equations for the chosen independent bare symbol,
quantifying all fixed arities and horizons, exact charge, local branch and parity actions.
This is *not* a claim of removal of regulator at positive order or of
comparison across physical couplings. See subtree. The all-orders problem requires normalization also
of coupling, OPE extraction and analytic estimates. Stage 0 has no T condition or homogeneous N.

We use the scheme's tree choice on even inversion torus and **continuous-center** convention;
top coupling powers before common denominator reading as in actual witness of Mixed; `adopt` uses
pure, filtration-compatible right inverse `physicalLabel` (earlier label lift Polynomials) and
engineering horizon `Born.born`. `Vertex.priced` applies to each axis used. These choices do not
use the unmarked vacuum coefficients or any asymptotic extraction from the actual hierarchy. Not
constructive-computable. The `uncut` prolongation (normalized iterated derivatives with coefficient power, of the indicated numerical polynomial, not exact-theory derivatives) uses finitely many earlier entries for any output coefficient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX
open Pert Pert.Position Maxwell Maxwell.Free Function Filter Set Jet Detector
open scoped Topology Classical BigOperators
variable {G:Gauge} (h:G.Simple)
structure Pay {G:Gauge} (h:G.Simple) {F:Labels.Frames G}(K:Bare.Shop F) (q:ℕ+) : Prop where
   square (d : ℕ): Recip F (nested F h K d).D
   lower (d e:ℕ)(b:d≤e)(v:Bank F e): zoomL F b ((nested F h K e).D v)=(nested F h K d).D (pulls (up F b) v)
   snaps (d:ℕ) : ∀ᶠ k:ℕ in atTop,(nested F h K d).D ∘ K.uncut h q k d=just ((nested F h K d).D (pureBank F d))∧IsUnit (motor F (K.ftReport h q k d 0))
   sticks (d:ℕ) : Tendsto (fun k=> K.ftReport h q k d 0) atTop (𝓝 0)
   frames (d e:ℕ)(b:d≤e): ∀ᶠ k in atTop,zoomL F b ∘ K.ftReport h q k e=K.ftReport h q k d
   conjs (d:ℕ):∃ f: (Bank F d →ₗ[ℝ] Bank F d), (f=pulls (par F d)) ∧ ∀ᶠ k in atTop, cPar F ∘ (K.ftReport h q k d)=turn (K.ftReport h q k d) ∧ f ∘ (K.uncut h q k d)=turn (K.uncut h q k d)
   anchor (d:ℕ)(i : Section F d): Tendsto (fun k=> lookie F i (K.uncut h q k d 0)) atTop (𝓝 (lookie F i (pureBank F d)))
-- fixed lift etc separate
lemma Pay.of {F:Labels.Frames G}(K:Bare.Shop F)(q:ℕ+)(hq:1<q.val): Pay h K q:= by
    refine ⟨fun _=>(nested F h K _).fixed,fun _ _ b v=> zoom_compat F h K b v,K.chamber h q hq,K.report_sticks h q hq,fun d e b=> K.report_up h q hq b,fun d=> ⟨_,rfl,(K.report_par h q hq d).and (K.uncut_par h q hq d)⟩,fun d s=>?_⟩
    let qP:= cross F s.p; simp_rw [Bare.Shop.uncut,pred_zero,cross_leaves]; rw [show lookie F s (pureBank F d) = cross F s.p (expose F s.f (pureBank F d),0) from Eq.symm (by rw [cross_market,market_zero]; rfl)] -- why simp_rw cross leads loops?
    apply (cross_smooth F s.p).continuous.continuousAt.tendsto.comp; exact (expose_leg (w:=fun k=> K.bank q k d 0) F (K.bank_white q hq) _).prodMk_nhds (K.report_sticks h q hq d)

/-- Attach to one coherent constructed family (rechoose witness in advances). -/
theorem single {p:ℝ}(hp:0<p)(f:Extraction.Order):∃ (C:Family G)(g:Extraction.Order) (S:Table C.book)(A:PertExtension.Actual C (f.refine g) S), C.Makes ∧ C.path.levels.clock.kernel.penalty=p∧ ∃ K:Bare.Shop C.labels, K.H=C.params∧K.S=C.localSection ∧ ∀ (q:ℕ+),1<q.val → Pay h K q:= by
   obtain ⟨C,hP,hM,hC,hB,hW,g,S,⟨A⟩⟩:= PertExtension.stamped_temple h p hp f
   exact ⟨C,g,S,A,hM,hB,⟨C.params,C.localSection,hM.sections,hP⟩,rfl,rfl,Pay.of h _⟩
end YM.PositionX
