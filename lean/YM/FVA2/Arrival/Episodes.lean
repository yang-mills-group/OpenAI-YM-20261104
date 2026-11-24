import YM.FVA2.XReg.Now
import YM.FVA2.Hearth.Posed
import YM.FVA2.Hearth.Epoch
/-!
 # Intermediate supplier: Epoch form of the prescription & MS comparison on those coefficients

 `Initialize` supplies stencil and orientation data; see `Register/` to assemble
 the full prescription (incl. regulator and position data) once and for all.
 At every regulator assemble the complete hierarchy (Epoch, with patch & inside &
 coupling trajectory & parameter convention). The epochs need not be constructed from
 the future MS comparison. Use even side family `XSpace.Run/Period`. Explicit field
 power reimbursements in `Hearth.Posed` and `Arrival.Top`. Recurrent transfers of
 full marked data & common trajectory `Gear`, not composing unrelated `Markov.step`
 estimates. See the modules in `FVA2/Facade` for the transfers.

 This proves identification also for all-order prescription with that coarsening. The
 finite and continuum position comparison hasn't been modified; in particular this
 doesn't claim the final grade and scale-law comparison.
 For the result including the final mass-independent frame and scale-law see
 `YM/FVA2/Main.lean`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival
open Function Filter Set MeasureTheory Metric Lattice Wilson
open MS MS.Koszul MS.Book MS.Book.Convolve Program MS.Native MS.Theater MS.Menus MS.Local.Physical MS.Land
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near MS.Rake Press XPos Change Slice
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking BlockGauge BlockGauge.Fabric OpenSlots.Quadratic
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Orb Facade Hearth RGComparison.Core16
open scoped Classical Topology BigOperators ContDiff

variable {G:Gauge} {n:Side} (Y:XSpace.Initialize G)
variable (E: Epoch G n) {J:Precision.ChartRatio G} (HJ:Precision.LocalRatio J)
namespace Episodic

-- Use `world` for the full moments in the common parameter.
local notation "K"=> Hearth.Epoch.clock E
local notation "Π"=> Hearth.Epoch.T E
local notation "z"=> Gear.loops K
local notation "v"=> Gear.priced K
variable (l:List (Folio G)) (b:List (Birth G))

 def candle : PowerSeries ℝ:= tally Π z v HJ (markValue Y l n)*(vacuum Π z v HJ)⁻¹
lemma candle_eq : candle Y E HJ l= Folio.coefficients Y n l := by unfold candle; rw [sold, Hearth.toll Y Π l z v HJ E.clock.first]
 def world : PowerSeries ℝ:= Birth.scan b ( candle Y E HJ )
lemma sum_world : world Y E HJ b= Birth.words Y n b:= congr_arg (Birth.scan b) (funext (candle_eq Y E HJ))

section Pressure
variable {W:Type}[LinearOrder W] (u:W→ MS.Rake.Label (Press.portDeck G))(M: Land.Prescription (Press.portDeck G)) (L: Cover) (d:W→Cover) (x:ℝ)(k:Finset W)
def start : MS.Book.Convolve.T ℂ:= Change.convertSources (Dictionary.paid u M x) k.toList (fun l=> substitute (Program.shift M.team x) (Slice.record (world Y E HJ (l.map (Top.declares u L d)))))
omit [LinearOrder W] in
lemma startup : start Y E HJ u M L d x k= Top.value Y u M L d n x k:= by unfold Top.value Episodic.start; simp_rw [sum_world]
lemma platform : PhysicalSum G M.team x n true k d L ( ApplyMF (Press.wickInput Y) ( Stripped M.team ) M u ) ( start Y E HJ u M L d x k ):= by rw [startup]; exact Top.tallies Y u M L d n x k E.F.even
end Pressure

section Determination
variable (w: E.F.Accounts→ ℝ→ℝ)(x:G.ColorIndex)(y:Flats G (Facade.Bottom E.F))
local notation "N"=> Facade.drive Π ( z ∘ some ) ( Facade.headquarters z )
local notation "V"=> (Folio.scenario Y n l)
local notation "q"=> Facade.collared Π z HJ v

-- announce actual formal coefficient ray to compare against, keep symbols same across any requested orders

lemma fully_charged (i:ℕ) (hw:∀ t,ContDiffAt ℝ ω (w t) 0)
        (he:∀ t, Through i (Facade.amount (w t)) (z t)) (k:ℕ) (hi:Folio.asset l + k ≤ i) :
      Lumen.Fk.read ( Hearth.localClimate Π y x w ) J (Hearth.tease Π x)
        ( Hearth.lens Π y x ( Hearth.rad Π V ) ) (Folio.asset l) k =
        PowerSeries.coeff k ( Stack.read y ( N (markValue Y l n) J q ).2 ) :=
    Hearth.prophecy Y Π l z v HJ x y w i hw he k hi

-- physical query with built-in clock, for *every* coefficient.
lemma eraVal (k:ℕ) :
      Lumen.Fk.read ( Hearth.localClimate Π y x (Gear.sheets K (Folio.asset l+k)) ) J
        (Hearth.tease Π x) ( Hearth.lens Π y x ( Hearth.rad Π V ) ) (Folio.asset l) k =
        PowerSeries.coeff k ( Stack.read y ( N (markValue Y l n) J q ).2 ) :=
    fully_charged Y E HJ l _ x y _ ( Gear.warm K _ ) ( Gear.charges K _) k le_rfl
end Determination

section Ready
variable {V:XSpace.Normalize.Store G} (K₁:XSpace.Rose.Pick V)(S:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (M: Land.Prescription (Press.portDeck G)) (h:G.Simple)

structure Mission (Y:XSpace.Initialize G) (M:Land.Prescription (Press.portDeck G)) : Prop
        extends Reg.SchemeV Y K₁ S M where
    comes (n:Side) (E:Epoch G n) {J:Precision.ChartRatio G} (p: Precision.LocalRatio J) {W:Type}
            [LinearOrder W] (u:W→Label (Press.portDeck G)) (d:Cover) (P:W→Cover) (x:ℝ) (s:Finset W) :
        PhysicalSum G M.team x n true s P d (ApplyMF (Press.wickInput Y) (Stripped M.team) M u)
          (start Y E p u M d P x s)
    stock (n:Side) (E:Epoch G n) {J:Precision.ChartRatio G} (p:Precision.LocalRatio J) (l:List (Folio G)) :
        candle Y E p l = Folio.coefficients Y n l
    herald (n:Side) (E:Epoch G n) {J:Precision.ChartRatio G} (p:Precision.LocalRatio J)
            (l:List (Folio G)) (x:G.ColorIndex) (y:Flats G (Facade.Bottom E.F)) (k:ℕ) :
        Lumen.Fk.read (Hearth.localClimate E.T y x (Gear.sheets E.clock (Folio.asset l+k))) J
          (Hearth.tease E.T x) (Hearth.lens E.T y x ( Hearth.rad E.T ( Folio.scenario Y n l )))
          (Folio.asset l) k = PowerSeries.coeff k ( Stack.read y ( Facade.drive E.T
            (E.clock.loops ∘ some) (Facade.headquarters E.clock.loops) (markValue Y l n) J
            (Facade.collared E.T E.clock.loops p E.clock.priced)).2 )

include h
/-- Intermediate supplier.
 `comes` identifies exact object on Master G n true for any d placement; `SchemeV.location`, etc
 give correlation comparison in X position scheme before the N adjustment.
 Use `clock` for the same **formal** multiscale calculations. Constructing
 appropriate analytic histories and comparing with this object would require additional
 work; nothing about that claimed.
 -/
theorem checkpoint5 (dial:Bool): ∃ M:Land.Prescription (Press.portDeck G), M.team=(Continuum.Continuation.proofStart h (Reg.supplies Y S) dial).team ∧ Mission K₁ S Y M:= by
 obtain ⟨M,hM,h⟩:= Reg.comparisonCP4 Y K₁ S h dial; exact ⟨M,hM,h,fun n E J p W _ u d P x s=> platform Y E p u M d P x s,fun n E J p=> candle_eq Y E p,fun n E J p=>eraVal Y E p⟩
-- also with existence if needed
omit h
lemma come_up (G:Gauge)(h:G.Simple)(dial:Bool): let Y:= XSpace.Initialize.standard G; ∃ (V:XSpace.Normalize.Store G)(K₁:XSpace.Rose.Pick V)(S:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (M:Land.Prescription (Press.portDeck G)), M.team=(Continuum.Continuation.proofStart h (Reg.supplies Y S) dial).team ∧ Mission K₁ S Y M:= by
 intro Y; obtain ⟨V,K₁,S,_,_⟩:= Reg.earns G h Y dial; exact ⟨ V,K₁,S,checkpoint5 Y K₁ S h dial⟩
end Ready
end Episodic
end YM.FVA2.Arrival
