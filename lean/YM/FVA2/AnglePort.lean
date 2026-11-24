import YM.FVA2.RankHistory
/-!
# Read all complete full-period conditional steps by Fk.read and Route.Bulk

Genuine palette.W values on FULL coarse and angular tags.H solver.User.Same birth from w.Need restore
 all Ledger prefactors (jac normalization makes up step vacuum update fee). Compute every Ticket
Polynomial through the included Fk & Route.Body $$S-prim:step penalty predictor exactly same$$.
Don't use Pose.`P.Steady` in arbitrary ambient.Awareness.Limit.Step. For top Offers documentary
Girth see later.Anchor this file to both analytic/q-local comparisons and MS.Bridge.Method.`θ`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory.Yurt
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.Sync
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Legacy Delay RayScatter Harvest
open MeasureTheory.Measure (IsAddHaarMeasure)
open RGComparison.Core16.Lumen
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}{I J:Type}[Fintype I][Fintype J]
variable (S:StepData c f)(T:Forest S.ratio)(Z:ChartRatio G)(hz:LocalRatio Z) (d:Descent n f)(hp:d.Room G)
variable (b:S.Choices)(t:d.Tags)(u:Pins G c)(z:ℕ→PowerSeries ℝ)
variable (h:Bid.Larger (G:=G) S)
local notation "E"=> Future G S T
local notation "K"=> Pins G c
local notation "Θ"=> gateQ S T b ( retained d t hp )
local notation "hQ"=> useful S T d t b h hp
local notation "I₀"=> retained d t hp
local notation "Ψ"=> fire S T b ( μLedger d Z t hp ( parentZ z ) ) Z (z 1)
local notation "δo"=> gate G S T

def meter (p:Quadratic (Pins G f))(A: Future G S T × Pins G c): ℝ:= p.flourish (gate G S T A)/2 + CityHistory.tax S T b A
lemma meter_form (p:Quadratic (Pins G f)): meter S T b p = (fun A=>p.flourish A/2) ∘ (( gate G S T ).toContinuousLinearMap)+( CityHistory.tax S T b ):= rfl
include h
lemma moment (p:Quadratic (Pins G f)): ContDiffAt ℝ ω (meter S T b p) 0:= by rw [meter_form]; exact ((Perch.analyticQ p).comp (( gate G S T ).toContinuousLinearMap.contDiff)|>.contDiffAt).add (tax_hot S T b h.1)
lemma payq (p:Quadratic (Pins G f))(v: E×K): (gateQ S T b p).flourish v=2*jet (meter S T b p) 2 v:= by
     let F(x):=p.flourish x / 2; let A:= ( gate G S T ).toContinuousLinearMap; rw [ meter_form, Inherit.plus (a:=F ∘ A) _ ((Perch.analyticQ p).comp ( A.contDiff )|>.contDiffAt) (tax_hot S T b h.1) v, GermLaplace.jet_pull A _ ((Perch.analyticQ p).contDiffAt.of_le le_top), Perch.chargeQ ]; change p.flourish (A v)+ ( Quadratic.genesis 1 ( CityHistory.tax S T b ) ).flourish v= _; rw [ Quadratic.native, show term 1 0=(1:ℝ) from PowerSeries.coeff_zero_one ]; unfold A; ring
omit h
-- launch-cost program.Decomposes per link step but model only reading, not asserting analytic grants.Fk.Prior weights =1 for fix one tag. Mom.Angle.
local notation "H" => Option (Edge (Site c))
local notation "ν"=> tangent G T.Free

def gauge_heat (p:Quadratic (Pins G f)) (x:Forge.Sky G T.Free): ℝ:= p.flourish (pext G S T (Inherit.down x))/2
def plank (x:Forge.Sky G T.Free)(u:Edge (Site c))(A:G.Color) := linkEnergy S (G.lieExp A * ( S.prediction (T.drape x) b u )⁻¹)
def payments (p:Quadratic (Pins G f))(a: Option (Edge (Site c)))(x:Lumen.Point G T.Free) := let y:= fun i=>launch (x.2 i); a.elim (gauge_heat S T p y) (fun i=> plank S T b y i x.1)

def tenants (p:Quadratic (Pins G f)) : Shelf G H T.Free := { «U»:= payments S T b p, R:=1, δ:=1/2, Q:=1,knot:=1/2, sector:=⟨1,1,1,zero_lt_one,zero_lt_one⟩ }
def sea (p:Quadratic (Pins G f))(u:Pins G c) : Planet ( tenants S T b p ) f T.Free (Option (Edge (Site c))) Unit := {
 loc:= fun e=> e.val.1
 root:= fun e=> Option.elim e 0 (fun i=> S.ratio.embed i.1)
 meter:=1
 cost x _ v i:= i.elim (gauge_heat S T p v) (fun j=> plank S T b v j (x • u j))
 glyph:=id
 stem _ j:= some j
 ray v:= v.elim 0 u }
local notation "Lx"=> sea S T b I₀ u

lemma destination (p:Quadratic (Pins G f))(x:ℝ)(v:Forge.Sky G T.Free): ((sea S T b p u).F x).action () v= gauge_heat S T p v+tagEnergy S b (T.drape v) ( expLinks G _ (x • u) ):= Fintype.sum_option ..
lemma harbour (p:Quadratic (Pins G f)): Fk.rise (sea S T b p u)=ᶠ[𝓝 0] charge (meter S T b p) 1 u:= by
   have he(i:T.Free): ∀ᶠ u:Fk.Door G T.Free in 𝓝 0, launch ( G.curvature ( Fk.spread u.2 i ))= Fk.spread u.2 i:= by
         refine (( ?_ : Tendsto (fun u:Fk.Door G T.Free=>Fk.spread u.2 i) (𝓝 (0:Fk.Door G T.Free)) (𝓝 1) ).eventually leaving); simpa [Fk.spread] using! (( show Continuous (fun u:Fk.Door G T.Free=> G.lieExp (u.2 i) ) from G.lieExp_cont.comp ((continuous_apply i).comp continuous_snd) ).tendsto (0:Fk.Door G T.Free))
   filter_upwards [ Filter.eventually_all.mpr he, (continuous_snd.tendsto (0:Fk.Door G T.Free)).eventually Inherit.down_left ] with y hx hy
   let F:= sea S T b p u; let v := Fk.spread y.2; have hv : (fun i:T.Free=>launch (G.curvature (v i)))=v:= funext hx
   have hm(i:Option (Edge (Site c))): Fk.postage F y i = F.cost y.1 () v i:= by cases i with|none=> exact congr_arg (gauge_heat S T p) hv|some e=> exact congr_arg (fun x=>plank S T b x e (y.1 • u e)) hv
   rw [Fk.rise,Fk.lapse, show (∑ i:Option (Edge (Site c)), Fk.postage (sea S T b p u) y i)= _ from (show ( ∑ i: H, Fk.postage F y i)=(F.F y.1).action () v from Finset.sum_congr rfl (fun i _=> hm i)), show (F.F y.1).action () v= _ from destination S T b u p y.1 v ];
   change y.1^2+_ = 1*y.1^2 + _; rw [one_mul,gauge_heat, show Inherit.down v=y.2 from hy ]; rfl

local notation "V"=> meter S T b I₀
abbrev promise (q:Ticket (Future G S T × Pins G c)):PowerSeries ℝ:= page ( sea S T b (retained d t hp) u ) Z u ( Harvest.shift (p:=meter S T b ( retained d t hp )) Z ( Ψ * q ) )
include h hz
lemma gross : PowerSeries.mk ( Fk.birth Lx Z ) * promise S T Z d hp b t u z 1=C (RayScatter.basePower Θ hQ u ν 1 * overhead Z T.Free) * Stack.read u (μLedger (Descent.push S T d) Z ((b,t):S.Choices × d.Tags) (show Descent.Room G (Descent.push S T d) from ⟨h,hp⟩) z):= by
    rw [ judgment S T d t b Z z h hp,promise,mul_one]; exact Harvest.income_all Lx Z hz (moment S T b h I₀) Θ (payq S T b h I₀) hQ u (harbour S T b u (retained d t hp)) _
lemma issued (A:Ticket ( Future G S T × Pins G c )) : Stack.read u (solenoid S T d t b Z z h hp A )= promise S T Z d hp b t u z A * ( promise S T Z d hp b t u z 1 )⁻¹ := by
     unfold promise; rw [mul_one]; exact full_order Lx Z hz (moment S T b h I₀) Θ (payq S T b h I₀) hQ u (harbour ..) _ (primeZ S T d t b Z z hz h hp) A
lemma solvable : 0 < Fk.birth Lx Z 0 ∧ PowerSeries.constantCoeff ( promise S T Z d hp b t u z 1 )=1:= by
    unfold promise; rw [mul_one]; exact ⟨ Fork.positive Lx Z hz (moment S T b h I₀) Θ (payq S T b h I₀) hQ u (harbour ..), Harvest.page_up Lx Z hz (moment S T b h I₀) Θ (payq S T b h I₀) hQ u (harbour ..) _ (primeZ S T d t b Z z hz h hp) ⟩
lemma route (L:Layout I (Future G S T))(U:Layout J (Pins G c)): let v:= logarithm Θ hQ Ψ L U; let q:= Sync.matrix (Γ:=Quadratic.RespectsPrice.inner hQ) L LinearMap.id; Route.Bulk.income q v=digital U (μLedger (Descent.push S T d) Z (b,t) (show Descent.Room G (Descent.push S T d) from ⟨h,hp⟩) z) ∧∀ r:Ticket (Future G S T × Pins G c),digital U (solenoid S T d t b Z z h hp r)= Route.Bulk.transfer q ( digital (across L U) (boost (Quadratic.center Θ hQ) r)) v:= by
    intro v q; constructor; · rw [ judgment S T d t b Z z h hp ]; exact RayScatter.generates Θ hQ ν Ψ L U (primeZ S T d t b Z z hz h hp)
    exact fun r=> RayScatter.digital_ink Θ hQ ν Ψ L U r (primeZ S T d t b Z z hz h hp)
end YM.FVA2.CityHistory.Yurt
