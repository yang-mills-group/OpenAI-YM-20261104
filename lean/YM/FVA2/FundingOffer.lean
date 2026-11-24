import YM.FVA2.AnglePort
import YM.RGComparison.Core16.Spool.Proof
import YM.RGComparison.Core16.Parcel.Pose
/-!
# Link to the existing _physical_ `Fk` generation on the FULL (not inversion) bare top

At every y.Rescales Parent V along that very y ray. `.Offers` hypotheses for this PARTICULAR
 analytic provider only (not assumed in our comparison theorems). Also give explicit nonemptiness
 of funding from `S.patch` even after choosing S with `Room` and that same physics.C. constants.Pose.
 (Useful alongside `RankHistory` on steps.J.Point.Search.Ansi.Empty tags tenant.Revenue.)
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory.Spot
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson PowerSeries Metric
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.Sync
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Legacy Delay RayScatter Harvest
open Pressure Forge.Hut
open MeasureTheory.Measure (IsAddHaarMeasure)
open RGComparison.Core16.Lumen RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
variable (S:StepData c f)(T:Forest S.ratio)(Z:ChartRatio G)(hz:LocalRatio Z) (b:S.Choices)(u:Pins G c)(z:ℕ→PowerSeries ℝ)
variable (h:Bid.Larger (G:=G) S)
local notation "E"=> Future G S T
local notation "K"=> Pins G c
-- Yurt had generic inherited meter Eq. For the first step CLARA.X.Sp exposes direct
-- Fk.read and harvest.prec formulas w0=1 special. Ledger z arbitrary? tax kernel uses z=w ratio internal.W.Block see.
local notation "d"=> Descent.nil (top:=f)
local notation "R"=> ( show (Descent.nil (top:=f)).Room G from trivial )
variable (v:(Descent.nil (top:=f)).Tags)
local notation "Θ"=> gateQ S T b (retained d v R)
local notation "hQ"=> useful S T d v b h R
local notation "μ"=> tangent G T.Free
local notation "I"=> gate G S T

def heat (x:Future G S T × Pins G c) := bareF G f (gate G S T x)+ CityHistory.tax S T b x
lemma form : heat (G:=G) S T b= (bareF G f ∘ ( I ).toContinuousLinearMap) + CityHistory.tax S T b:= rfl
lemma splitTop : heat (G:=G) S T b= (bareF G f ∘ ( gate G S T )) + CityHistory.tax S T b:= rfl
lemma finance (x:E × K) : heat S T b x= _root_.YM.Wilson.energy (T.drape ( expLinks G _ x.1 )) + tagEnergy S b (T.drape (expLinks G _ x.1)) (expLinks G _ x.2):= by unfold heat; change bareF _ _ (pext _ _ _ _)+_= _; unfold bareF; rw [ inserts ]; rfl
include h
lemma thermalHeat : ContDiffAt ℝ ω (heat (G:=G) S T b) 0:= by rw [ splitTop ]; exact (leaned _ (born_hot ..)).add ( tax_hot S T b h.1 )
lemma precisionHeat (x:E × K): (Θ).flourish x=2*jet (heat S T b) 2 x:= by
    let g:= bareF G f; let L:= (I).toContinuousLinearMap; have he:ContDiffAt ℝ ω g (L 0):= by rw [map_zero]; exact born_hot ..
    rw [ form, Inherit.plus (b:=CityHistory.tax S T b) _ (he.comp (f:=L) 0 L.contDiff.contDiffAt) (tax_hot S T b h.1) x, GermLaplace.jet_pull L g ((born_hot ..).of_le le_top) ]; change (retained d v R).flourish (L x)+(Quadratic.genesis 1 (CityHistory.tax S T b)).flourish x= _; rw [Quadratic.native, ← frozen (r:=v),show term 1 0=(1:ℝ) from coeff_zero_one,one_mul ]; ring

-- adapt from Offers Vox. truly propagate through full Fk.read. θ.Metadata for same S,T.
variable (P:Oven S.patch)(X:P.Form G)(H:P.Offers X S.kernel)(he:∀ i,‖u i‖≤ X.Q)
local notation "FkU"=> RGComparison.Core16.Spool.lens (S:=S) u X T
lemma handed (P:Oven S.patch)(X:P.Form G)(u:Pins G c)(x:ℝ): ( RGComparison.Core16.Spool.lens (S:=S) u X T ).F x= RGComparison.Core16.Forge.Hut.seam S T ( RGComparison.Core16.Parcel.Oven.slice u x ):= by rcases S with ⟨k,U,b⟩; rfl -- namespace Hut via Forge?
include H he
lemma runs : ( FkU ).Steady := by cases S; apply Oven.paints T H he h
lemma wages : ∀ᶠ x:Fk.Door G T.Free in 𝓝 0, 0≤x.1 → Fk.rise (FkU) x=charge ( heat (G:=G) S T b ) 1 u x:= by
    let J:= ball (0:G.Color) X.δ; let K₀:Set ( RGComparison.Core16.Forge.Sky G T.Free ):= {x|Planet.crisp X.δ Finset.univ x}; have hu: ∀ᶠ x:Fk.Panel G T.Free in 𝓝 0, Fk.spread x∈ K₀:= by
        have he := Fk.deckspace (ι:=T.Free) X H.good; exact he.mono (fun z h=> Planet.crisp_negligible _ _ ( half_le_self H.good.extent.1.le ) le_rfl h )
    filter_upwards [ (continuous_fst.tendsto (0:Fk.Door G T.Free)).eventually (gt_mem_nhds H.good.thick.2.1), (continuous_snd.tendsto (0:Fk.Door G T.Free)).eventually hu ] with x hx hw h0
    rw [ Fk.wages (runs S T u h P X H he) x ⟨h0, le_of_lt (show _ from hx)⟩ hw b, Spot.handed S T h P X u x.1, RGComparison.Core16.Forge.Hut.action_eq ]; change x.1^2+_ = 1*x.1^2+ heat S T b (recover u x); rw [one_mul,finance]; rfl
omit H h he
lemma aligned {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U][FiniteDimensional ℝ U]
   {f g: ℝ × U→ℝ}(hf: AnalyticAt ℝ f 0)(hg:AnalyticAt ℝ g 0)(hh:∀ᶠ x:ℝ × U in 𝓝 0,0≤x.1→ f x=g x): f=ᶠ[𝓝 0] g:= by
    obtain ⟨r,hr,hR⟩:=Metric.nhds_basis_ball.mem_iff.mp ( hh.and ( hf.eventually_analyticAt.and hg.eventually_analyticAt ) ); let V:=Metric.ball (0:ℝ×U) r
    have he x (hx:x∈ V) : (0≤x.1→f x=g x) ∧ AnalyticAt ℝ f x ∧ AnalyticAt ℝ g x:= hR hx
    let y:ℝ × U:=(r/2,0); have h0 : y∈V:=mem_ball_zero_iff.mpr (by rw [Prod.norm_def,Real.norm_of_nonneg (show 0≤ y.1 from (half_pos hr).le), show y.2=0 from rfl,norm_zero]; exact max_lt (half_lt_self hr) hr)
    have ht : f=ᶠ[𝓝 y] g:= by filter_upwards [Metric.isOpen_ball.mem_nhds h0,(continuous_fst.tendsto y).eventually (lt_mem_nhds (show 0<y.1 from half_pos hr)) ] with x hx hv; exact (he x hx).1 (show 0<x.1 from hv).le
    have hfg:= ( show AnalyticOnNhd ℝ f V from fun i hi=> (he i hi).2.1 ).eqOn_of_preconnected_of_eventuallyEq ( fun i hi=>(he i hi).2.2 ) (convex_ball (0:ℝ × U) r).isPreconnected h0 ht
    filter_upwards [Metric.ball_mem_nhds (0:ℝ × U) hr] with x hx; exact hfg hx
include h H he
theorem prospect : Fk.rise (FkU)=ᶠ[𝓝 0] charge ( heat (G:=G) S T b ) 1 u := aligned ( Fk.bump_hot ( runs S T u h P X H he )|>.analyticAt ) ( charge_hot 1 u (thermalHeat S T b h)|>.analyticAt ) ( Spot.wages S T b u h P X H he )

-- the top step, in z=1 clock; U.Next interactions labelled. Also z with supplements use method of Yurt.Corr.Declare classical special.
local notation "ε"=> chargeStep S T Z b (1:PowerSeries ℝ)
local notation "V"=> heat S T b ( G:=G )
local notation "Ψ"=> Fork.interaction Z V
local notation "W"=> fire S T b ( μLedger d Z v R (parentZ 1) ) Z 1
local notation "ν"=> Stack.read u
omit he H in
lemma fusionL : W = Fork.interaction Z V:= by
    let Kp: Ticket (Future G S T × Pins G c):= boost (LinearMap.fst ℝ E K) (OpenSlots.tissue Z T.Free); let a:= pay 1 (( bareF G f ) ∘ gate G S T ); let F:= CityHistory.tax ( G:=G ) S T b;
    unfold fire; rw [ CityHistory.stock ]; change boost (gate G S T) (chip 1 (bareF G f)) * ( Kp* chip 1 F )= _; rw [pullPay _ 1 _ ( born_hot G f ) ]; unfold Fork.interaction;
    let J:= (( bareF G f ) ∘ gate G S T ); change exponential (pay 1 J) * (Kp* exponential (pay 1 F))= Kp* exponential (advancing V); rw [mul_left_comm _ Kp];
    rw [ ← OpenSlots.compose_two _ _ ?_ (OpenSlots.stipend _ _ (CityHistory.Legacy.price_stat S T b h.1)) ]; swap; · apply OpenSlots.stipend; apply Inherit.stable ( leaned (gate G S T) (Legacy.born_hot G f)); rw [Function.comp_apply,map_zero,bare_zero]; exact fun x=> energy_nonneg _
    congr 2; let a₁:= (( bareF G f ) ∘ gate G S T ); have hx:Radial.Stationary a₁:= by
        apply Inherit.stable ( leaned (gate G S T) (Legacy.born_hot G f)); rw [Function.comp_apply,map_zero,bare_zero]; exact fun x=> energy_nonneg _
    rw [ Delay.exp_vac0 (f:=J) hx, Delay.exp_vac0 (f:=F) (price_stat S T b h.1), Spot.splitTop ]; unfold advancing; let g:= rise J; let k:= rise F; rw [ ExactTower.up_add (x:=J) (y:=F) hx.smooth (price_stat S T b h.1).smooth ];
    have he {u w:Ticket (Future G S T × Pins G c)}: Stack.drop 2 (u+w)= Stack.drop 2 u + Stack.drop 2 w:= by apply PowerSeries.ext; intro i; unfold Stack.drop; rw [map_add,coeff_mk,coeff_mk,coeff_mk,map_add]
    rw [neg_add, he, map_add,map_add ]; abel
include hz
-- optional top direct across physically material size.Data.On.CoreH before z.Transport from lens t.
theorem earns_true (A:Ticket (Future G S T × Pins G c)): Stack.read u (solenoid S T d v b Z 1 h R A)= page FkU Z u A:= by
    rw [Harvest.pages FkU Z hz (thermalHeat S T b h) Θ (precisionHeat S T b h v) hQ u (prospect S T b u h P X H he) ]; unfold solenoid; rw [Pi.one_apply,fusionL S T Z b h v]; rfl

omit hz H he
-- horizon-independent/coupling order planner `P.Fund` does not discharge all analytic comparison costs.
lemma enough (u:Pins G c): ∃ Y : P.Form G,P.Offers Y S.kernel ∧ (Spool.lens (S:=S) u Y T).Steady ∧ ∀ i, ‖u i‖≤ Y.Q:= by
    let q:=1+‖u‖; have hp : 0<q:= by unfold q; positivity
    obtain ⟨X,hX,he⟩:=Oven.fund P h.1 q hp
    have hx:∀ i,‖u i‖≤X.Q:= by intro i; rw [hX]; apply le_trans (norm_le_pi_norm ..); unfold q; linarith
    exact ⟨ X,he,runs S T u h P X he hx,hx⟩
end YM.FVA2.CityHistory.Spot
