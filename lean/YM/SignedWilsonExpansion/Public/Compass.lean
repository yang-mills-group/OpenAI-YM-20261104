import YM.SignedWilsonExpansion.Public.World
/-! # Normalization in the elected file

These are the margins for the framed *physical* fields; the true continuum scale is still
held fixed when these fields are chosen. Order-one signed signal is at cap six (`money` of the
thermometer is distinct from the order-two test of the next file). Coordinates `LogV` used
by `Coupling.running` use minus log distance. Coefficients with a `ν` always use the `Main`
MS mass-scale log convention, *not* the small length (the overlap test stresses this).

Leading approximations, meter at nearest original Wilson spacing `Trace.Pilot.wilson`,
coherence & orientations, determining elections, precision preservation across bounded positive
radius ratios (with bounded inverses). Overlap estimates are actual little-o through the given
order, all such ratios, including taking slightly higher orders to price simultaneous errors.
-/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.Answer.ContinuumLimit.Vision
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped Classical Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}{f:Extraction.Order}
variable {Z:WilsonPrescription G} {dial:Bool}(V:Vision E f)(Q:Perspective H Z dial)
abbrev Meter : ℝ→ℝ:= Trace.Pilot.wilson V.pupil.Z
abbrev Signal (Z:WilsonPrescription G)(r:ℝ):ℂ:= WilsonPositionThermometerReading.tested V.pupil.last (Pre Z V) Z.criterion r
abbrev cT (Z:WilsonPrescription G):ℝ:= Rose.c_T Z.criterion
local notation "Θ"=> V.T Z
abbrev oriented (V:Vision E f)(W:ℝ→tower V.pupil.S) (d:ℕ): Prop:= ∀ᶠ r in trail, walk W r d ( Normalize.leaf G d )=V.pupil.S.unit d ∧ (∀x:Sec G d, walk W r d ( reel d x )=V.pupil.S.conj V.pupil.last.room.kernel.spin d (walk W r d x))∧∀ (s:Signed)(x:Sec G d),walk W r d ( ori s.ortho d x )=V.pupil.S.mirror V.pupil.last.room.kernel.spin d s (walk W r d x)

local notation "Ξ"=> V.Pre Z
local notation "Ω"=> V.Post Z
variable {ι:Type} (l:Filter ι) (κ ξ:ι→ℝ) -- κ radius, ξ log shift
local notation "τ"=> ( (Θ) ∘ κ )
local notation "κ₀"=> ( SignedWilsonExpansion.Kane.Tilted.jump κ ξ )
abbrev shiftClock (ν:ℝ)(b:ℕ):= ( (Θ) ∘ κ₀ - Tone τ ξ ( GroupS.ψ Z.criterion Q.MS ν ) b )=o[l] ( τ ^ b )
abbrev shiftPost (ν:ℝ)(d b:ℕ):= SeatsW.Discount ℂ l (τ^b) (fun i=> bend (Ω) (κ i) (κ₀ i) d - Crisis.gate d (ξ i) ( Classroom.Levy (gaugeN Z.scheme Z.criterion Q.MS ν) τ ξ b i d ))
abbrev shiftPre (ν:ℝ)(d b:ℕ):= SeatsW.Discount ℂ l (τ^b) (fun i=> bend (Ξ) (κ i) (κ₀ i) d - readyL (V:=Z.criterion) (Y:=Q.MS) ν τ ξ b i d )
variable {l κ ξ}

local notation "λ₀"=> (Rose.c_T Z.criterion:ℂ)
structure Compass : Prop where
   -- the actual calendar. TRUE field Leading and θ oriented. Doesn't depend on argument number or order.
   calendar : Frames.Crest V.pupil.last V.pupil.J Z
   comparator : Tendsto (fun m=> coeff 1 ( Rose.Detector Z.scheme Z.criterion m ) ) Front (𝓝 (Rose.c_T Z.criterion :ℂ)) ∧ Scale.Select.output Z.criterion ( Scale.Measure.start Z.scheme Z.criterion 6 ) = ( Rose.c_T Z.criterion:ℂ ) • PowerSeries.X
   meter : Coupling G (Meter V)
   first_price : IsEquivalent trail (Θ) (Meter V) ∧ (fun r=> Signal V Z r - λ₀ * ( Meter V r:ℂ))=o[trail] (Meter V)
   c_neg : cT Z<0
   c_paid (r:ℝ): cT Z * V.T Z r=(Signal V Z r).re
   leading : PhysMS.Leading V.pupil.last (Pre Z V)
   determined (d:ℕ): ∀ᶠ r in Trace.Pilot.trail, (Z.store.measure d).D (WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r)=(Z.store.measure d).D (XSpace.Normalize.reference G d)
   spin (d:ℕ): oriented V ( V.Pre Z ) d ∧ oriented V ( V.Post Z ) d
   inclusion (b d:ℕ)(q:b≤d):∀ᶠ r in trail,∀ x:Sec G b, window Z V true r d (Normalize.up q x) = V.pupil.last.sector.derivatives.rise q ( window Z V true r b x ) ∧ window Z V false r d (Normalize.up q x)= V.pupil.last.sector.derivatives.rise q ( window Z V false r b x )
   follows : Crisis.Implements Z.scheme Z.criterion trail (fun i d=> Frames.Native Z (V.T Z i) d) (V.T Z)
   equality (d:ℕ) : ∀ᶠ i in trail,∀ x, walk (V.Post Z) i d x=walk (V.Pre Z) i d (Frames.Native Z (V.T Z i) d x)
   signal_for_every_character (b:ℕ)(p:0<b)(w:ℝ→ Viewers V.pupil.last) : (fun i=> Lark.thermometer Z.criterion ( Frames.coreValue V.pupil.last V.pupil.J Z id w ) i - ( Rose.c_T Z.criterion:ℂ ) * ( Θ i:ℂ )) =o[trail] ((Θ)^b)
   adjacent_every {ι:Type}(l:Filter ι)[l.NeBot](r σ:ι→ℝ)(q:Tendsto r l trail)(p:FO l σ)(ν:ℝ)(d b:ℕ)(n:0<b): shiftClock V Q l r σ ν b ∧ shiftPre V Q l r σ ν d b ∧ shiftPost V Q l r σ ν d b
   chamber (D:ℕ)(d:0<D){a:Axis}{S:SignedWilsonExpansion.Camera.Plans a}(X:SignedWilsonExpansion.Vault.Author.CameraT S)(b:ℕ)(L:XSpace.Run)(q:ℕ)(positive:0<q)(gear:L.ratio=(3:ℕ)^q): Nonempty ( Calendar Z V L X D d b )

lemma clockG : Coupling G (Meter V):= wilson_link V.pupil.last H V.pupil.bliss.budgets V.pupil.bliss.keen V.pupil.bliss.lies
lemma guides (q:Tendsto κ l trail)(p:FO l ξ) [l.NeBot](ν:ℝ)(d b:ℕ)(n:0<b): shiftClock V Q l κ ξ ν b ∧ shiftPre V Q l κ ξ ν d b ∧ shiftPost V Q l κ ξ ν d b:=by
     let B:= V.marks_the_data Z Q; let L:= V.pupil.WFrame Z.store; let D:= V.pupil; obtain ⟨P,R⟩:= Frames.maturity D.last D.J D.VFrame.2 Z Q.matching ν κ ξ q p B L n D.VFrame.1 d; exact ⟨ R, Frames.guide D.last D.J Z Q.matching ν κ ξ q p B L n d,P ⟩ -- order after b1 arg?

lemma certificate : Compass V Q:=by
     let B:= marks_the_data Z V Q; let L:= V.pupil.WFrame Z.store; let D:=V.pupil; obtain ⟨t,p,r⟩:= Frames.Crest.finances Z Q.matching
     refine ⟨ B,⟨ t,p ⟩, V.clockG, Frames.Crest.nearer D.last D.J D.VFrame.2 Z Q.matching id tendsto_id B L D.VFrame.1 V.sc D.foundation _ V.clockG,r, ?_, L, fun d=> D.marked Z.store d, ?_,?_,Frames.mature D.last D.J Z Q.matching id tendsto_id B.clock, fun d=> Frames.postP (h:=H) D.last D.J D.VFrame.2 Z id tendsto_id D.VFrame.1 d,Frames.illuminated D.last D.J D.VFrame.2 Z Q.matching id tendsto_id B L D.VFrame.1 V.sc D.foundation,fun l _ r σ p h => guides V Q p h, fun D d _ _ T x L q s c=> fundedVisit Z V L T D d x q s c ⟩
     · intro r; exact Frames.Crest.accurately D.last D.J Z Q.matching B r
     · intro d; exact ⟨ SpinW L ( r:=id ) tendsto_id d,Frames.spins (h:=H) D.last D.J D.VFrame.2 Z id tendsto_id D.VFrame.1 L d⟩
     intro b d q; filter_upwards [ risePlot L q ( r:=id ) tendsto_id, Frames.rise D.last D.J D.VFrame.2 Z Q.matching D.VFrame.1 _ _ q ] with i hi hp x; constructor; · exact hp x
     exact hi x
end YM.Answer.ContinuumLimit.Vision
