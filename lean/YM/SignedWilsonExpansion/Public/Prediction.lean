import YM.SignedWilsonExpansion.Public.Compass
import YM.SignedWilsonExpansion.Contrast.Gall

/-!
# Both configurations in one calibrated frame

Fields at **the same** r, not W(2 r). Geometry `Test`: compactly supported smooth on
`conf 3`. Continuum periods at fixed r with noncollision at support upstairs (`Prism`).
`Rose.Badge` = subset of {0,1,2}. `Buffet.cumul` = third connected formula on these.

This is on the original Wilson correlations in the FULL UV and then extracted period
limit **on fixed fields**, as well as (in the short-distance asymptotic part) on
any admitted character phase. No statistic on finite realizations of a character
assumed. `phase V` uses the OPE ensemble / kernel space rules. At each period and
cut, `boundE` (in Frames.Galleria the continuum) is implemented with all seven
(original, normalized) expectations. `IntegratedPhysicalCutoff` is this LIFE test;
same normalized profile convention throughout.

The other equally important finite-cutoff version (the purchased weak plate used to
prove the comparison) will be spelled out separately: not an assertion that the two
kinds of microscopic labels agree at cut! (They agree *as physical field classes*:
fixed and weak representations use their respective limit/equivalence.) `Perspective`
used here for the independent *calculation*. You can in particular ask both for the
comparison for a given prescription Z and for the `Perspective` before deploying
any physical program. No relation of `Perspective.MS` or Z to Vision data is assumed.

Axis in this test is 3. E is `WickFace.lens G` (`WickFace.blaze`, spatial 1,2 curl;
 Lean basis numbering, Wick polynomials). Scalar product and Casimir as in `MS.Land`.
Conjugation / reflection of Cast inherited from elected convention. `Bump` criterion
`Admire` is PURELY INDEPENDENT. Any sufficiently narrow bump can be made before data.
-/

set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.Answer.ContinuumLimit
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book
open PhysMS PhysMS.Frame Next.UVStress Order
open Belfry Belle OPE OPE.Orbits MeasureTheory Asymptotics FullVolume
open Carbon Frames Museum
open scoped Classical Topology ContDiff BigOperators
universe u
variable {G:Gauge} {Z:WilsonPrescription G}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}{f:Extraction.Order}
variable (V:Vision E f) (N:WilsonPrescription G) -- Q implicitly Z
variable {dial:Bool}(Q: Perspective H Z dial)(x:Scale.Stage 3)(φ: Test 3)(ν r:ℝ)(a:Bool) -- a=true means post
namespace Vision
abbrev phase:= Viewers V.pupil.last
abbrev sections:= if a then V.Post N else V.Pre N
variable (u:Viewers V.pupil.last)(W:ℝ→ tower V.pupil.S)
-- Life statement for either version. Does NOT use ν offsets from MS.
abbrev planeMoments (i:Rose.Badge)(z:Points 3) : ℂ:= PlotW V.pupil.last W u r 4 3 z ( Contrast.maskE G i )
abbrev ConnectedU (φ:Test 3)(v:Viewers V.pupil.last)(r:ℝ):ℂ:= Carbon.aggregate φ ( planeMoments V r v ( sections V N a ) )
abbrev ConnectedV_raw (φ:Test 3)(v:Viewers V.pupil.last)(r:ℝ):ℂ:= ConnectedU V N a ( ProbeB.double φ ) v r
abbrev ConnectedV (φ:Test 3)(v:Viewers V.pupil.last)(r:ℝ):ℂ:=(2:ℂ)^12*ConnectedV_raw V N a φ v r
abbrev momentsAtCutoff (U P:ℕ)(u:Ps U P E.paths.family 3)(i:Rose.Badge):ℂ:= Museum.tableaux E.paths V.pupil.last V.colours ( sections V N a ) r i ( Contrast.testE G 3 ) U P u
abbrev IntegratedPhysicalCutoff (U P:ℕ):ℂ:= ∑u:Ps U P E.paths.family 3,Museum.mass E.paths.family φ r U P u * Buffet.cumul ( momentsAtCutoff V N r a U P u )
-- notation trap: τ id.L noise only at fixed. θ: bound error orders
abbrev hasContrastOrder (a:Bool)(φ:Test 3) {ι:Type}(L:Filter ι)(k:ι→ℝ)(s:ι→Viewers V.pupil.last) : Prop:= (fun i=> ConnectedU V N a φ (s i) (k i)- ConnectedV V N a φ (s i) (k i) - ProbeB.quote ( four N ) φ 2 * (( V.T N ( k i ):ℝ ):ℂ )^2 ) =o[L] (( V.T N ∘ k ) ^ 2 )
/-- One theorem uniform across phases. Clock comes from Z by measured calibration, same
    gauge independent test *without* using normalization Rose.c_T for the predicted log coefficient.

    `h` extractor ordinary moments including all faces all measurements; life holds for one
    joint integral INCLUDING products of proper faces. Intrinsically separates the true fixed
    campaign calibration from the working secant weak-plate audit. `Lift` is stronger than
    the quoted equality that position-vs-post calibrations don't change the orientation.
    Convergence on independent schedules for both profiles, post and pre. Include `Front` optical
    theorem separately when generalizing la carte placements. The expansion pays all powers
    here through `Perspective.matching`. -/
structure Prediction (V:Vision E f)(Q: Perspective H Z dial) (ν:ℝ) : Prop where
   calibrated : Compass V Q
   implemented (a:Bool) : ∀ᶠ k in trail,∀ (U P:ℕ), E.paths.family.ref 4 ≤ U → ∀ (u:Ps U P E.paths.family 3)(m:Rose.Badge), momentsAtCutoff V Z k a U P u m= ∫ y,(∏ j∈m,E.paths.family.O U P (( V.Cast Z a k 4 ) ( WickFace.lens G )) (u j) y) ∂(law G _ (E.paths.family.beta U P))
   life (a:Bool)(φ:Test 3)(τ:ℝ)(ht:0<τ): (Homes.track V.pupil.f).limits (fun p=>Museum.Prism E.paths.family.S (tsupport φ) p τ) ( IntegratedPhysicalCutoff V Z φ τ a ) ( ConnectedU V Z a φ none τ )
   independentRemoval (φ:Test 3)(j:ℕ): Tendsto (fun k:ℕ=> Carbon.lamp Z ( Z.run.step k ) j φ) atTop (𝓝 ( ProbeB.raw ( four Z ) φ j )) ∧ Tendsto (fun k:ℕ=> Medi.dol Z ( Z.run.step k ) j φ) atTop (𝓝 ( ProbeB.raw ( Carbon.Medi.G4 Z ) φ j ))
   jacobian (φ:Test 3)(x:Points 3):ProbeB.double φ x=(( (2:ℂ)^12 )⁻¹)* φ ( (2:ℝ)⁻¹ • x )
   testOnDouble (φ:Test 3)(F:Points 3→ℂ):(ProbeB.double φ).applyTo F=φ.applyTo ( fun x=>F ( (2:ℝ) • x ))
   Lift (i:ℕ)(h':i≤2)(φ:Test 3):ProbeB.quote (Medi.G4 Z) φ i=ProbeB.quote (four Z) φ i
   third (φ: Test 3): ProbeB.quote (four Z) φ 0=0∧ProbeB.quote (four Z) φ 1=0∧ ProbeB.quote (four Z) φ 2=(Real.log 2) • φ.applyTo ( ProbeB.money ( ProbeB.gain Q.MS Z.scheme Z.criterion ν ) )
   axis (x:Scale.Stage 3)(hx:WickFace.Holds x):ProbeB.criterion (four Z) 0 x.val = (( (8*Fintype.card G.ColorIndex*WickFace.pay x 0 1*WickFace.pay x 0 2*WickFace.pay x 1 2):ℝ ):ℂ ) ∧ ProbeB.receipt (four Z) 2 x.val=( Real.log 2*G.casimir/(16*Real.pi^2) ) • ProbeB.criterion (four Z) 0 x.val
   independentTestable (x:Scale.Stage 3)(hx:WickFace.Holds x)(o:ℝ)(hp:0<o):∃ϕ:RealTest 3, ProbeB.Admire (four Z) x ϕ ∧ tsupport ϕ ⊆ Metric.ball x.val o
   compared {ι:Type} (L:Filter ι)(r:ι→ℝ)(k:Tendsto r L trail)(s:ι→Viewers V.pupil.last)(φ:Test 3)(a:Bool): hasContrastOrder V Z a φ L r s
   sign {ι:Type} (x:Scale.Stage 3)(ϕ:RealTest 3)(hx:ProbeB.Admire (four Z) x ϕ) (L:Filter ι)(r:ι→ℝ)(k:Tendsto r L trail)(s:ι→Viewers V.pupil.last): star ( ProbeB.quote (four Z) (Rose.coerce ϕ) 2 )= ProbeB.quote (four Z) (Rose.coerce ϕ) 2 ∧ 0 < ( ProbeB.quote (four Z) (Rose.coerce ϕ) 2 ).re ∧ ∀ᶠ i in L,0 < ( ConnectedU V Z false ( Rose.coerce ϕ ) ( s i ) ( r i ) - ConnectedV V Z false ( Rose.coerce ϕ ) ( s i ) ( r i ) ).re -- post also via Lift + compared
set_option maxRecDepth 3200 in
lemma pricePlane : Prediction V Q ν:=by
      let D:=V.pupil; have h0:= D.VFrame.1; have hv:= D.VFrame.2; have hp:= D.WFrame Z.store; let h:= Q.matching; have T:= V.marks_the_data Z Q
      refine ⟨ V.certificate Q, ?_, ?_, fun φ i=>⟨ Carbon.roots Z Q.matching ν φ i,( Medi.limi Z h φ i ).comp h.onSchedule⟩, ProbeB.expanded,ProbeB.expands,fun i hi f=> Medi.changeTicket Z h ν f i hi, ?_,Carbon.axisP Z h ν, ?_, ?_,?_⟩
      · intro a; cases a
        exact Eventually.mono ( tickets D.last D.J Z id tendsto_id hp V.colours ) (fun i hi U P he v p=> hi U P he p v)
        exact ( Galleria.storyPost (h:=H) D.last D.J hv Z id tendsto_id hp h0 V.colours ).mono (fun i hi U P he v p=> hi U P he p v)
      · intro a φ τ ht; cases a
        exact chronicle (h:=H) D.last D.J Z τ φ V.colours D.TrackU D.trackV ht
        exact Galleria.chronicPost (h:=H) D.last D.J Z τ φ V.colours D.TrackU D.trackV ht
      · intro φ; have he:=clockE Z h ν Carbon.podium φ; exact ⟨he.1, he.2.1, he.2.2.1⟩
      · intro x hx o t; exact excellent Z Q.matching ν x hx t
      · intro ι L r k s φ a; cases a
        exact actual D.last D.J hv Z h ν r k T hp h0 V.sc D.foundation φ s
        exact Galleria.rResults D.last D.J hv Z h ν r k T hp h0 V.sc D.foundation φ s
      intro ι x ϕ hx L r k s; exact ⟨ ( plank Z h ν x ϕ hx ).1,( plank Z h ν x ϕ hx ).2, readyWorld D.last D.J hv Z h ν r k T hp h0 V.sc D.foundation s ϕ x hx⟩
end Vision
end YM.Answer.ContinuumLimit
