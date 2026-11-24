import YM.FVA2.Singular
/-!
# Track exact seam costs and ALL optional full-cover conditional branch choices

 No theorem that these additional defect tickets (not the generator-canonical residual estimates
 used for MS endpoint) are small.Here just exact receipts with the corrected contracted costs.
 They should be paid on this or any other proved equivalent system IF using qlocal expansions on
 full cover steps. For MS formal-to-formal comparison recall the other route directly proved
 removal of inversion/canonical generator residuals.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {f c n:Side} (he:Even f.val)
-- Frame estimator of *relative* correction. Not log yet.Account.B.T
local notation "H"=> Both.orb G f he
local notation "F"=> Pins G f
local notation "O"=> Flats G f

def Δs (V:Ticket (Pins G f))(W:Ticket (Flats G f)): Ticket (Flats G f):= W^2 * Return ( boost (Trans.coverL G f) V )
lemma spectrum {V:Ticket (Pins G f)}(hp: incline V)(W:Ticket (Flats G f)): Δs V W * boost ( Trans.coverL G f ) V=W^2:= by unfold Δs; rw [mul_assoc,mul_comm (Return _), spend_it (preserve_boost _ hp),mul_one]
lemma seats {V:Ticket (Pins G f)}(hp: incline V){W:Ticket (Flats G f)}(hs:incline W): incline (Δs V W):= pool (by rw [pow_two]; exact pool hs hs) ( investment ( preserve_boost _ hp ) )
include he in
lemma terrain (t:(Descent.nil (top:=f)).Tags) (J:ChartRatio G)(z:ℕ→PowerSeries ℝ):
    Δs ( μLedger Descent.nil J t trivial z ) ( initialFull G f (z 0) ).W=1:= by rw [Δs, CityHistory.stock, ← show ( H ).ε= Trans.coverL G f from rfl, bootPay he, pow_two ]; exact spend_it (pool (OpenSlots.restores (z 0) ( OpenSlots.firstBill (G:=G) (n:=f))) (OpenSlots.restores (p:=firstBill) _)) -- add hc argument?

variable (S:StepData c f)(h:S.patch.Branches S.kernel G) (hc:Even c.val)(b:S.Choices)(J:ChartRatio G)(hJ:LocalRatio J)
local notation "T"=> Forestry S
local notation "P"=> canopy S
local notation "K"=> Both.orb G c hc
local notation "Y"=> Both.lights G S he
local notation "Z"=> Mirror.House.join Y K
local notation "M"=> Future G S T
local notation "Eo"=> Cross (G:=G) S P
local notation "lo"=> Flats G c
local notation "ξ"=> gate G S T
variable (w:PowerSeries ℝ)(V:Ticket (Pins G f))(hp:incline V)(U:Unmasked G f)
local notation "A"=> ( fire S T b V J w )
local notation "B"=> receipt P b J w U
local notation "τ"=> blankRight ( canopy S )
include hp h hJ
lemma invoice_step : B^2 = boost ( blankRight P ) (Δs V U.W) * boost (Z).ε A:= by
    rw [ receipt, fire, mul_assoc ( boost ( blankRight P ) U.W ), map_mul ( boost (Z).ε ), Both.producer S h he hc b J hJ ];
    rw [ mul_pow, ← mul_assoc,show boost (Z).ε (boost ξ V)=boost τ (boost (Trans.coverL G f) V) from ?_,← map_mul (boost τ), spectrum hp, map_pow ];
    apply Stack.into; rintro ⟨x,y⟩; rw [caught,caught,caught,caught, show ξ ((Z).ε (x,y))= _ from Both.gate_ε S he y x hc ] -- order

-- attach full at exactly the boundary.L.Student.Support.Api do after.
omit hp h hJ
end YM.FVA2.Both
