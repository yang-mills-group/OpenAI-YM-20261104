import YM.TraceExtension.Agora
import YM.TraceExtension.Link.Esc
import YM.TraceExtension.Link.Identity

/-!
# Leading trace coefficient, high-energy limit and free-field exclusions

`main` fixes a simple compact gauge image, a positive kernel penalty and
an initial extraction order. It produces a calibrated Wilson family and
a refinement on which a final table exists. `Result` then applies to every
final table on that family and refinement.

`XScheme` positions the grade-four fields using unselected correlations
and fixes their shell normalization. Its coupling test uses the free stress
label on those positioned fields. `FieldComparison` gives the measured
stress tensor, the centered trace coefficient and its Wilson normalization
at positive lengths tending to zero.

The Euclidean trace asymptotic and the spectral measure in `HighEnergy`
refer to the selected vacuum. Rescaling the inverse length to infinity
gives the stated limits on compact and Schwartz tests, and on joint
two-point Wightman tests. The limiting measure on the forward cone has
density proportional to the square of the Minkowski quadratic form.

`Exclusion` rules out the specified Wick-polynomial two-point forms and the
stated Maxwell Fock comparisons on symmetric transverse waves, with their
vacuum matrix-element and projection hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Target
open Function Filter Set Extraction MeasureTheory OS Spec Boundary Table Mink Spin
open Spec Over Pilot Pith Sundial Terrace Verse Link TraceExtension Photons
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators Classical
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (h : G.Simple)
local notation "F₀" => Climb.Bel C.book

/-- Cap-four positioning by `PlotX` and its leading off-diagonal jet limits, followed by the shell normalization of the scalar and shear components relative to the same position map. -/
structure XScheme (H : (Climb.Bel C.book).Hierarchy)(l : Ultrafilter (ℕ × ℕ))
    (P P' : ℝ → change S 4) (χ : E4 → ℝ) : Prop where
    plotted : PlotX F H l h P
    leadingOffDiagonal : ∀ m : ℕ, ∀ᶠ r in trail, chores r (P r) m
    posed : ∃ x y : ℝ → ℝ, Posed H h P P' x y
    norm : ShellNorm P' χ

/-- Stress comparison at physical lengths. The tensor coefficient κ tends to one. The scalar coefficient differs from d₂ times the squared running coupling by O(g⁴), with d₂ = −b₀/2 in the final result. The centered trace uses that same scalar coefficient in the selected-phase tests. -/
structure FieldComparison (H : (Climb.Bel C.book).Hierarchy) (Z : Arch C)
    (P P' : ℝ → change S 4) (κ d e : ℝ → ℝ) : Prop where
    alignment : Another F (H:=H) P' P -- .spun gives AlignV
    positions : ∀ m : ℕ, ∀ᶠ s in trail, chores s (P' s) m
    /-- actual tensor equality, translations/Wards from F -/
    measures : ∀ᶠ s in trail, Measures F s (P' s) (κ s) (d s) (e s)
    spinTwo : Tendsto κ trail (𝓝 1)
    /-- inherits also the leading Peano coefficient `-b0/2`
    tested with ANY same-normalized coupling (`TendC.measures`). -/
    leading : TendC F P' d
    /-- same Wilson normalization through the pertinent order.
    `glo` measures the coupling in X space. -/
    calibrationX : Tendsto (fun i => glo P' i / wilson Z i) trail (𝓝 1)
    wilson : Coupling G (Pilot.wilson Z) -- positive and leading log
    coupling : Coupling G (glo P')
    /-- even parity jet through λ=g^2; O(g^4) here even numerical
    on these exact choices. (Its displayed toSigned values in `sign_d`.) -/
    coefficient_O : (fun i => d i - d2 G * (glo P' i)^2) =O[trail] (fun i => glo P' i ^ 4)
    traced_O : (fun i => 4 * d i - (-2*b0 G)*(glo P' i)^2) =O[trail] (fun i => glo P' i ^ 4)
    centerComparison : ∀ᶠ s in trail,
        s^(4:ℕ) • TraceExtension.center F=
          (4*d s) • TraceExtension.centerIn S (selected F) (P' s (stepField C))
    selectedScalar : ∀ x : Points 2,x ∈ conf 2 →
        Tendsto (fun s=> S.classMoment (selected F) (fun _=>4) (s • x) (fun _=> P' s (stepField C))) trail
           (𝓝 ((F₀).classMoment (F₀) (fun _=>4) x (fun _=>stepField C)))
    /-- The E diagnostic in the selected phase (coupling test uses
      unselected). `bauble` is the exact normalized one-loop slope. -/
    selectedE : Tendsto (fun i=> (eSelected F P' i).re / Pilot.wilson Z i ^ 2) trail (𝓝 (bauble C))

/-- High-energy positive measure convention. -/
structure HighEnergy (μ : Measure E4) : Prop where
    spectral : TraceSpectrum F μ
    compact (φ : E4 → ℂ) (hc : Continuous φ) (hk : HasCompactSupport φ) :
        Tendsto (fun ρ : ℝ => Zlog ρ • ∫ p:E4, φ (ρ⁻¹ • p) ∂μ)
          atTop (𝓝 ((award G / (1536 * Real.pi)) • ∫ p:E4 in cone, Mink.m p^2 • φ p))
    schwartz (φ : Probe E4) :
        Tendsto (fun ρ : ℝ => Zlog ρ • ∫ p:E4, φ (ρ⁻¹ • p) ∂μ)
          atTop (𝓝 ((award G / (1536 * Real.pi)) • ∫ p:E4 in cone, Mink.m p^2 • φ p))
    relative (φ : Probe E4) :
        letI := spectral.upper
        letI := cone_temperate (award_pos h).le
        Tendsto (fun ρ => Zlog ρ • TraceExtension.relative μ (condense ρ φ)) atTop
          (𝓝 (TraceExtension.relative (coneMeasure (award G)) φ))
    joint (φ : Joint 2) :
        Tendsto (fun ρ => Zlog ρ • F.A.world.W 2 (pairV F.action.J (pinned F)) (condense ρ φ))
             atTop (𝓝 (∫ p:E4, waveTest φ p ∂coneMeasure (award G)))

/-- Exclusions for the specified Wick-polynomial pairings, Maxwell Fock vacuum matrix elements and projected local comparisons. -/
structure Exclusion : Prop where
    wick_polynomial (Color : Type u) (pairing : TraceExtension.Wick.Palette Color)
        (q w : TraceExtension.Wick.PolyField Color) :
        ¬ ∀ (x y : Probe E4), HasCompactSupport ⇑(waveTest (productTest x y)) →
          F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest x y)=pairing.wicks q w (waveTest (productTest x y))
    noMaxwellFock (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n) : Comparison F U → ¬ Nfl F U
    projected (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n) (r : ℝ) :
        Comparison F U → 0 < r → ¬ Regions r F U

/-- Public surface. `.general` exposes several finer universal assertions,
including leading validated at this *formal* invariant order also under weaker
compatibility conditions (Lantern.leading), Ward determining square in the
PlotX pre-normalization, and spectral integrability. -/
structure Result : Prop where
    general : Arena.{u} F h
    d₂ : d2 G= -b0 G/2
    positive : 0 < award G
    /-- nonvacuity of shell normalization and actual Wilson calibration,
    then actual comparison in any XScheme at that H and l. -/
    stress : ∃ (H : (Climb.Bel C.book).Hierarchy) (Z : Arch C) (l : Ultrafilter (ℕ × ℕ)),
       Bliss F l Z H ∧ (∃ χ P P', XScheme F h H l P P' χ) ∧
       ∀ χ P P', XScheme F h H l P P' χ → ∃ κ d e, FieldComparison F H Z P P' κ d e
    realAdjoint : F.action.J (pinned F)=pinned F
    scalar : ∀ g : Lorentz, F.action.spin.rail g (pinned F)=pinned F
    centered : ∀ v : Probe E4,
        inner ℂ F.action.operators.vacuum (excitation F.action.operators (pinned F) v)=0
    identity (v : Boundary.Test4) :
        F.action.operators.field (pinned F) v =
          F.action.operators.field (S.pin 4 (stressTrace F.sector.energy)) v -
           (euclideanVEV S (selected F) (stressTrace F.sector.energy) * ∫ x,v x) •
             LinearMap.id (R:=ℂ)
    nonzero : pinned F ≠ 0
    shortDistance : EuclideanAsymptotic F (award G)
    law : ∃! μ, HighEnergy F h μ
    exclude : Exclusion.{u} F

include h in
lemma fieldComparison_of {H : (Climb.Bel C.book).Hierarchy} {Z : Arch C}
    {P P' : ℝ → change S 4} {κ d e : ℝ → ℝ}
    (ha : Another F (H:=H) P' P) (hP : ∀ m, ∀ᶠ r in trail, chores r (P' r) m)
    (he : Tendsto (fun i => glo P' i / Pilot.wilson Z i) trail (𝓝 1))
    (hW : Coupling G (Pilot.wilson Z)) (hX : Coupling G (glo P'))
    (ht : TendC F P' d) (hκ : Tendsto κ trail (𝓝 1))
    (hc : ∀ᶠ i in trail, Measures F i (P' i) (κ i) (d i) (e i))
    (hO : (fun i=> d i-d2 G * (glo P' i)^ (2:ℕ)) =O[trail] fun i=> glo P' i^ (4:ℕ))
    (hE : EuclideanAsymptotic F (award G)) : FieldComparison F H Z P P' κ d e:=by
   refine ⟨ha,hP,hc,hκ,ht,he,hW,hX,hO,?_,center_eq F _ _ ht,
       uncentered_scalar F h _ _ _ hX ht hE, e_position_check F h _ _ _ _ _ H hW ht hE hc hκ (ha.spun.mono fun i hi=> hi.align.unit)⟩
   rw [show (fun i=> 4*d i - (-2*b0 G)*(glo P' i)^2)=(fun i=>4*(d i-d2 G*(glo P' i)^2))
       from funext (fun i=>by rw[force_b]; ring)]
   exact hO.const_mul_left _

lemma assembled (hr : Arena.{u} F h) : Result.{u} F h:=by
   obtain ⟨μ,hμ,-⟩:= hr.strong
   refine ⟨hr,force_b G,award_pos h, ?_, self_adjoint F,pinned_scalar F,
       pinned_centered F,Identity.center_field F,hr.trace_nonzero,hr.crest.at_length,?_,hr.exclude,hr.crest.nfock,
       fun n U r hU hR=>hr.projected n U r hR hU⟩
   · obtain ⟨H,Z,l,X'⟩:= hr.stage
     obtain ⟨P,hp,hL⟩:= X'.height
     obtain ⟨χ,hχ⟩:= Work.A05.has_window Pith.sail Pith.sail_at
     obtain ⟨P',x,y,hx,hX⟩:= (X'.sees P hp hL).zenith χ hχ
     refine ⟨H,Z,l,X'.past,⟨χ,P,P',hp,hL,⟨x,y,hx⟩,hX⟩,?_⟩
     rintro φ Q Q' ⟨hQ,hR,⟨s,t,hS⟩,hχ⟩
     obtain ⟨ha,hP',he,hF,a,d,e,hf,hg,hM,hB⟩:= (X'.sees Q hQ hR).moves φ Q' s t hS hχ
     exact ⟨a,d,e, fieldComparison_of F h ha hP' he X'.slope hF hf hg hM hB hr.crest.at_length⟩
   exact ⟨μ,⟨hμ.measure,(fun p h h'=> (hμ.compact p h h').2.2),fun p=> (hμ.schwartz p).2.2,
       hμ.relative,hμ.wight⟩,fun ν hν=> hν.spectral.unique hμ.measure⟩

/-- For each positive penalty and initial order, a calibrated Wilson family admits a final table on a refinement, and every final table there satisfies the trace result. -/
theorem main (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b) (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
       Extraction.Wcmain C ∧ ∃ q : Extraction.Order,
       (∃ S : Table C.book, Nonempty (Final C (p.refine q) S)) ∧
       ∀ (S : Table C.book) (F : Final C (p.refine q) S), Result.{u} F h := by
   obtain ⟨C,hC,hK,hB,hW,g,S,hS,hF⟩:= agora.{u} b hb p h
   exact ⟨C,hC,hK,hB,hW,g,⟨S,hS⟩,fun S F=> assembled F h (hF S F)⟩

end YM.Trace.Target
