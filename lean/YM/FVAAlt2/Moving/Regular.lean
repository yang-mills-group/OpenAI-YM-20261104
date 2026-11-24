import YM.FVAAlt2.Moving.Lane
import YM.FVAAlt2.Moving.Priority
/-!
# Common protocol through all finite demand supports.
$R fixed before smoothing. p-periods arbitrarily exceed epoch lower bound. Benchmark uses ample regulator (above M's purchases); no power law assumption on coupling growth and no upper bound on periods needed or assumed of schedule. Request this before posing Field Y etc. All parsable quantities. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Study
open Function Set Filter MeasureTheory Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT Pegs
open MS MS.Land MS.Menus MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open Integration RunFormalChain Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home YM.FVAAlt2.Home.Report
open Labels Extra.FD Maxwell Source Extraction FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop Perot
open PowerSeries (C coeff constantCoeff)
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{K:KernelChoices}{X:Type}
variable (Y:Oracle.Program K)(Z:∀ B:Patch,B.Branches K G)(C:Run G)(R:Lodge.Contract C Y Z) (t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B"=> (R.profile Y Z C t ht)
local notation "P"=> (Period.Field.LodgeT.instance_real Y Z C R t ht)
local notation "Γ"=> C.family.path
set_option quotPrecheck false
variable (F:Calibration.Tent (( R.profile Y Z C t ht).entire)) {g:G.ColorIndex}(p:ℕ)
variable {u:MS.Local.Physical.Deck G}{J:Booked u} (H: MS_Data G J) (T: MS.Land.Prescription u)(μ:ℝ)
variable {n:ℕ} (Λ:X→ℕ) (a:X→ Cover)
-- choose epochs after p & all possible orders along ℓ.S.Auth.Higher.Before.Engine.X_PH does not constrain independently chosen masks at any period.
abbrev Holding (l:Filter X) : Prop:= ∀ n d:ℕ,∃ σ:X→ℕ,Sound.Margin (I:=Fin n) Y Z C R t ht F p d T μ σ ∧ ∀ᶠ x in l,σ x ≤ Λ x
variable (l:Filter X)(hV:Tendsto t l atTop)
-- ANY sufficiently large periods can be used with all reservations.
include hV
lemma hold_all: ∃ Λ₀:X→ℕ, ∀ Λ:X→ℕ,(∀ᶠ x in l,Λ₀ x ≤ Λ x)→ Holding Y Z C R t ht F p T μ Λ l:=by
 choose σ h using fun n d=> Sound.guards Y Z C R t ht F (I:=Fin n) p d T μ
 let f(x:X):=∑ n ∈ Finset.range (t x),∑ d∈ Finset.range (t x),σ n d x; refine ⟨ f,fun x hx n d=>⟨σ n d,h n d,?_⟩⟩
 filter_upwards [hV.eventually (eventually_gt_atTop n), hV.eventually (eventually_gt_atTop d),hx] with i hi hv he; exact le_trans (le_trans (Finset.single_le_sum (f:=fun d=>σ n d i) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hv)) (Finset.single_le_sum (f:=fun n=>∑ d∈Finset.range (t i),σ n d i) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hi))) he -- annotate
omit hV
local notation:max "S!"=> ( Top.outdoor C.family.params (basisR C) )
def Plan := Top.outdoor C.family.params (basisR C)
local notation:max "F₀"=> C.family.labels
-- bank from actual periodic reading weights
abbrev ledgerL (x:X): Perot.Exhibit B x F₀:= fun (_ :ℕ) v=> Figure.perRead C Z P (fun _ j=> a x+ Lattice.lift (v j)) (sheet F) (Λ x) ( (B).stop.choose x )
local notation "terms" x:max=> ledgerL Y Z C R t ht F Λ a x
local notation "m"=> (R.profile Y Z C t ht)
noncomputable def Rack₁ (x:X) := (fun d:ℕ=>takeReal ∘ ( Perot.Raw B x ( terms x ) (Plan C) d ))
lemma young (x:X) : ∀ n b d i,RSpec ((terms x) n b d i):= by intro n b d i; apply RSpec.real_co; intro v; unfold ledgerL Figure.perRead; rw [PowerSeries.coeff_mk]; simp
variable (hG:G.Simple)
local notation:max "M"=> Home.seats (Plan C).liftOff (Plan C).certified
variable {J':Booked (Home.seats (Plan C).liftOff (Plan C).certified)}{H:MS_Data G J'}(τ:MS.Land.Prescription (Home.seats (Plan C).liftOff (Plan C).certified))(hT:Top.Output C.metals.O (Plan C) H τ μ)
variable (h:Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p)(Hq:∀ x,p≤ t x)(hver:(R.profile Y Z C t ht).VenueT a)
variable (hx:Holding Y Z C R t ht F p τ μ Λ l)
open FormalOPE.RG10.Carryon FormalOPE.RG10.Position
open YM.FVAAlt2.Moving.Budget
set_option quotPrecheck false
local notation:max "A_" x:max=> ( Perot.turned B x (Plan C) μ τ ( terms x ) )
local notation:max "V_" i:max=> ( RG10.Position.Deck C.family.labels i )
include hV hG hT h Hq hx l hver
-- all-period sturdy budget
open Finset in
lemma employs {d:ℕ} [l.NeBot] [l.IsCountablyGenerated] (v:Home.Datum (V_ d)): Nice p l (fun x=> A_ x d v) (Home.Report.science μ H C.family.labels d v):=by -- d binder
 have hm:(fun x:X=> A_ x d v )=fun x:X=> Home.mix ( takeReal ∘ report (nativeR (Plan C)) B x (terms x) τ μ) ((dout C.family.labels M d).map PowerSeries.C) v:= funext fun x=> congr_fun (Perot.exact_economic _ _ _ (Study.young Y Z C R t ht F Λ a x) _ ) v
 rw [hm]; apply Nice.use; rintro ⟨⟨i,f⟩,z⟩ j hj
 obtain ⟨σ,hσ,hx'⟩:= hx i d
 refine Pegs.valueAt hG Y Z C R t ht F p d (Lobby.owner ∘ z) τ H μ Λ a (Complex.continuous_re.comp f.continuous) f.hasCompactSupport (E:=tsupport f) ?hs f.tsupport_subset l hV h hver Hq hT.draw.high hσ hx' ?_ j hj
 · exact fun i hi=> subset_closure ( fun v=>hi ( show _= (0:ℝ) from by unfold comp; rw [v];rfl) )
 intro j; exact high (z j)
-- Ready at knots and adjusted health.Logbook counted arity eventually all, not necessarily same unique ρ(Λ) across smoothing eras.
local notation:max "o" x:max=> ( Plan C ).stock x
local notation "Φ"=> (R.profile Y Z C t ht)
noncomputable def warp (x:X):= Convert.depart (Plan C) τ μ (( B ).L x) (( B ).batch x)
abbrev seat (x:X):= Convert.fares ( Plan C ) τ μ (( B ).L x) ( (B).batch x )
local notation:max "π_" x:max=> warp Y Z C R t ht μ τ x
local notation:max "λ_" x:max=> seat Y Z C R t ht μ τ x
local notation "ρ"=> (Rack₁ Y Z C R t ht F Λ a)
omit hV hG hT h Hq hx l hver
lemma authenticity (x:X)(d:ℕ) : A_ x d = extra (Rack₁ Y Z C R t ht F Λ a x) (π_ x) (λ_ x) d:=by
 let E:= Perot.Raw B x (terms x) (Plan C) d; refine congr_arg (fun w=> Home.mix w ((λ_ x) d)) ( funext (fun i: Home.Datum (V_ d)=> ?_) ) -- frame. 
 change PowerSeries.subst _ (takeReal (E i)) = _; exact ( Warp.turning (π_ x) (takeReal (E i)) ).symm

private abbrev Y0 := Home.Report.science μ H C.family.labels
variable [l.NeBot][l.IsCountablyGenerated]
include hV hG hT h Hq hx l hver
local notation "TZ"=> (warp Y Z C R t ht μ τ)
local notation "Γ₁"=> seat Y Z C R t ht μ τ
local notation "D₁"=> ( Plan C ).stock
local notation "H₁"=> Home.Report.science μ H C.family.labels
local notation "Ν"=> ( Plan C )
open YM.FVAAlt2.Moving.Budget
lemma enhanced : YM.FVAAlt2.Moving.Budget.Preparation p l ( Study.Plan C ) TZ Γ₁ ρ H₁ := by
 refine ⟨fun x d=> Convert.tired μ Ν C.metals.O hG C.alloy.B.ratio hT.draw _ _ d,fun d=> tendsto_const_nhds.congr (fun i=>Eq.symm ( Convert.taxable μ Ν C.metals.O hG C.alloy.B.ratio hT.draw ( ( B ).L i ) d (( B ).batch i) )), fun i v=> physics _ _ _ v, ?_ ⟩
 intro d v; simp_rw [ ← authenticity Y Z C R t ht F μ Λ a τ ]; exact employs Y Z C R t ht F p μ Λ a l hV hG τ hT h Hq hver hx v
omit hV hG hT h Hq hx l hver
def Normal (x:X): Rack C.family.labels:= mintRack ( Row (Rack₁ Y Z C R t ht F Λ a x) ( ( Plan C ).stock ) )
include hV hG hT h Hq hx l hver
variable (he:0<p)
local notation "ζ"=> ( enhanced Y Z C R t ht F p μ Λ a l hV hG τ hT h Hq hver hx )
lemma sees (d:ℕ) : listens (l:=l) (D:=D₁) (fun x:X=> ρ x d) ∧ ∀ᶠ x in l, Row ( extra (ρ x) (TZ x) (Γ₁ x) ) D₁ d=(TZ x).charge ∘ Row (ρ x) D₁ d:= heard ( Study.Plan C ) ((hT.credit Top.age).certified) ζ d
lemma officialCredential (d:ℕ):∀ᶠ x in l,Credible D₁ (Rack₁ Y Z C R t ht F Λ a x d):= RG10.Carryon.credential ((hT.credit Top.age).certified) _ (sees Y Z C R t ht F p μ Λ a l hV hG τ hT h Hq hver hx d).1
include he
lemma near_s : Tendsto (fun x:X=>coeff 1 (Convention (Row ( ρ x ) D₁ )).x ) l (𝓝 1):= YM.FVAAlt2.Moving.Budget.pre_slope Ν ((hT.credit Top.age).certified) ζ hT.hot he.ne' fun _=> Convert.leaving ..
lemma near_money : ∀ᶠ x in l, ( Convention (Row (ρ x) D₁ ) ).Hot:= YM.FVAAlt2.Moving.Budget.readyK Ν ((hT.credit Top.age).certified) ζ hT.hot he fun _=> Convert.leaving ..
variable (Gd:Drivers) (Y':Patience (Study.Plan C) Gd)
local notation "Peanut"=> Normal Y Z C R t ht F Λ a
local notation:max "κ" => (hT.credit Gd)
include Y'
lemma phaseOK (d:ℕ)(v:Home.Datum (V_ d)): Nice p l (fun i=> Normal Y Z C R t ht F Λ a i d v ) ( Y'.Yield v ):= by
 have hv := YM.FVAAlt2.Moving.Budget.chosen Ν Y'.certified ζ hT.hot he ( fun i=> Convert.leaving .. ) d v
 rw [← Convert.Y_eq Ν H τ Gd C.metals.O μ hG Y'.certified C.alloy.B.ratio hT.draw.high (Convert.tired μ Ν _ hG C.alloy.B.ratio hT.draw) hT.hot Y'] at hv; exact hv
-- now brings CHECKG (RG10) equality at all horizons on chosen OCC.P.Inventory phase.Marquee.
variable {w : (i:ℕ)→ Matrix ( RG10.Position.Deck C.family.labels i ) ( RG10.Position.Deck C.family.labels i ) (PowerSeries ℝ)}
lemma checkG (hZ:Mass.Framed (Study.Plan C) Y' w) (d:ℕ)(v:Home.Datum (V_ d)): Nice p l (fun i=> Home.mix (Normal Y Z C R t ht F Λ a i d) (w d) v) ( mix (( Convert.f Ν μ H ).charge ∘ H₁ d ) ( Mass.ζfinal Ν μ H d ) v ):= by
   rw [← (hT.msbar Gd Y' d hZ)]; apply Nice.use; exact phaseOK Y Z C R t ht F p μ Λ a l hV hG τ hT h Hq hver hx he Gd Y' d
end YM.RegulatorIR.FVAAlt2.Moving.Study

