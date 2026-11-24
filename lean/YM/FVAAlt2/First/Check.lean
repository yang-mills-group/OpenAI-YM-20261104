import YM.FVAAlt2.First.Spaces
import YM.Pert.Rig.Linked
/-! Smear-through-null $Pert.Full branch (measurements WILL use its first-order Peak certificate). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Subspace
open Function Finset Filter Topology Lattice
open Set Metric MeasureTheory
open MS MS.Koszul MS.Menus MS.Book MS.Theater MS.Tone MS.Vista MS.Fleet MS.High MS.Tide MS.Orbit MS.Rake MS.Dial MS.Land
open Extraction PertExtension.Position
open Pert PertExtension PertExtension.LatticePT Profiles
open Pairing
open Real
open PowerSeries (C coeff)
open scoped Topology BigOperators ContDiff PowerSeries
variable {d:ℕ}{q:Side}{n j:ℕ}{K:Set (Points d)} (μ:ℝ)
variable {G:Gauge} {B:Local.Physical.Deck G}
variable {D:Precision.ChartRatio G}(hD:Precision.LocalRatio D)
local notation "u"=>StepP q K
local notation "Φ"=> poster q K μ
variable (P:Prescription B) {U:Booked B}(S:MS_Data G U)(p:Fin d→ Rake.Label B)(hG:G.Simple)(hq:1<q.val)
abbrev Tprod (q:Side)(i:ℕ):= Full.Grid ( Full.period q i ) d
local notation "ξ"=> Full.topSpacing
local notation "Bμ"=> boardX P
abbrev earn (q:Side)(j:ℕ)(x:Tprod (d:=d) q j) := Bμ (μ-Θ q j) p x (ξ q j)
lemma earn_point (i:u)(k:ℕ): cash P p Φ μ k i= coeff k (earn μ P p q i.level i.x) := by
 unfold cash; rw [enoughCash]; change coeff k ( Bμ (μ-Θ q i.level) p (fun z: Fin d=> wrap (dimT (Φ).side i) ((Φ).head i+(Φ).off z i) ) (ξ _ _) )=_; rw [visit_k]; apply congr_arg (fun z: Tprod (d:=d) q i.level=> coeff k (earn μ P p q i.level z)); funext z; rw [map_add]; exact (by change wrap _ (Lattice.lift _)+wrap _ (Lattice.lift (i.x _ - _))=_; rw [wrap_lift,wrap_lift];abel)
variable (hv:TaylorOKPl S (ExtraBook B) P)
include hD hG hq hv
lemma reimbursement (hk:IsCompact K)(hx: K⊆conf d)(k:ℕ): ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,∀ x:Tprod q i, Full.embedding (ξ q i) x∈K → ‖coeff k (earn μ P p q i x)-area S p μ k (Full.embedding (ξ q i) x)‖≤ C*exp (-mildG* Θ q i):=by
 obtain ⟨-,C,hC,h⟩:=visits_β P p hD S (books μ hq hk hx) hG hv k; rw [stopP,eventually_comap] at h; refine ⟨C,hC,h.mono ?_⟩; intro i he x w; obtain he:= he (⟨i,x,w⟩:u) rfl; rw [ Pi.sub_apply, earn_point, framesS ] at he; exact he
lemma arriv (k:ℕ): Rig.Arrives (Rig.routine q hq) (fun i x=> coeff k (earn μ P p q i x)) (conf d) (area S p μ k):= by
 intro σ hσ z hz g ht; let f(i:ℕ):= Full.embedding (ξ q (σ i)) (g i); let w(i:ℕ):=area S p μ k (f i); change Tendsto f atTop _ at ht; obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp ((conf_open d).mem_nhds hz); let K:= Metric.closedBall z (r/2); have hh:0<r/2:= half_pos hr
 let y(i:ℕ):= coeff k (earn μ P p q (σ i) (g i)); obtain ⟨C,hC,H⟩:= reimbursement μ hD P S p hG hq hv (show IsCompact K from isCompact_closedBall ..) (show K⊆conf d from (Metric.closedBall_subset_ball (half_lt_self hr)).trans hR ) k
 have he : PeakT atTop { θ:= Θ q ∘ σ,η:=0,room:=fun i=> theta_nonneg q _ } mildG (y-w):= ⟨ C,hC,((hσ.eventually H).and ( ht.eventually (Metric.closedBall_mem_nhds z hh) ) ).mono fun i h=> h.1 _ h.2 ⟩
 have hl:Tendsto w atTop (𝓝 (area S p μ k z)):= (Dial.contin S p _ (realize_one hz) _ _ μ|>.1).tendsto.comp (realize_s.continuousAt.tendsto.comp ht)
 have hu:= (PeakT.topos mild_p ( show Tendsto (Θ q ∘ σ) atTop atTop from ( grows hq ).comp hσ ) he ).add hl; rw [zero_add] at hu; exact (by change Tendsto y _ _; rw [← sub_add_cancel y w]; exact hu)
omit hD hG hq hv
local notation "CZ"=> PowerSeries ℂ
variable (f:Test d)
def pcanon(f:Test d)(z:Points d):= Complex.re (f z)
def psmear (q:Side)(i:ℕ)(f:Test d)(F:Tprod (d:=d) q i→CZ): CZ:= ∑ j:Tprod (d:=d) q i, C ((ξ q i:ℂ)^(4*d) * f (Full.embedding (ξ q i) j)) * F j
-- defined after reg D step
abbrev castF (q:Side)(i:ℕ):=psmear q i f (earn μ P p q i)
lemma integrableA (k:ℕ): Integrable (fun x=> f x*area S p μ k x):= f.smearing fun x hx=> (( contin S p _ ( realize_one hx ) _ _ μ|>.1 ).comp realize_s.continuousAt ).continuousWithinAt
include hD hv hG hq
lemma logs (k:ℕ): Tendsto (fun i:ℕ=> coeff k ( castF μ P p f q i)) atTop (𝓝 (∫ x:Points d,f x*area S p μ k x)):= by
 obtain hx:= Rig.grid_limit f.continuous f.hasCompactSupport f.tsupport_subset ( arriv μ hD P S p hG hq hv k ); apply hx.congr; intro i; unfold Rig.reporting castF psmear; simp only [Rig.routine,PowerSeries.coeff_C_mul,map_sum, Finset.mul_sum, mul_assoc]; rfl
omit hv
variable {H:Source.Hol G}{L:Labels.Frames G} (R:Lobby.Registry L H)
include R
lemma forecastR (k:ℕ): coeff k (Profiles.forecast S p μ (pcanon f))= (∫ x: Points d, f x* area S p μ k x ).re :=by
 obtain ⟨Y,hY⟩:= MS.Land.High_stopsPl hG S (Lobby.Table R B); rw [forecast, PowerSeries.coeff_mk ]; refine Eq.trans ?_ (integral_re (integrableA μ S p f k)); apply (integral_congr_ae (f:=(fun x:Points d=> pcanon f x * (area S p μ k x).re)) (g:=(fun x:Points d=> (f x*area S p μ k x).re))); filter_upwards with x; by_cases he:x∈ conf d; · obtain h:= Profiles.area_jet (q:=q) D R S Y p μ hD hq hG hY he k; rw [ ← h ]; simp [ Complex.mul_re,pcanon ]
 simp_rw [pcanon,f.vanishes he,zero_mul,Complex.zero_re,zero_mul]
include hv
theorem costOrder : AlignSeries atTop (fun i:ℕ=> takeReal ( castF μ P p f q i )) ( forecast S p μ (pcanon f)):=by intro k; change Tendsto (fun i:ℕ=> coeff k (takeReal (castF μ P p f q i))) atTop (𝓝 (coeff k (forecast S p μ (pcanon f)))); rw [forecastR (q:=q) μ hD S p hG hq f R k ]; simp_rw [takeReal,PowerSeries.coeff_mk]; exact Complex.continuous_re.continuousAt.tendsto.comp ( logs μ hD P S p hG hq hv f k )
end YM.FVAAlt2.Home.Subspace
