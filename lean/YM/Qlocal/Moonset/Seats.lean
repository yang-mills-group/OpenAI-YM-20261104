import YM.Qlocal.Moonset.Meadow
/-!
One-step support and budget quote for curvature re-expression plus coupling reset in the marked
Taylor comparison. Buys size of the book (Σ powered forward/back reproduction, relative to
unit exponential analytic input) and uncertainty price (while estimating the **result**, keeps the
globally known true beta of parent mesh).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau Wheel
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
open Aux Aux.Name Push.PriceCompiler Kinetic.Port
open Aero Sienna Further.PhysicalPeriodLimitF933
namespace PostDebt
variable {r:Stage} {q:ℕ}
open Wheel Wheel.Ride Wheel.Ride.Pair Aero Step Step.PlanV Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D':RG.Supply.Rolls X.p}(S:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) (hx:4≤x)
set_option quotPrecheck false
local notation "κs"=> Burn.horizon q
local notation "LΩ"=>D'.L x
local notation "I"=>Card D' S x y hx κs
local notation "Tp"=> X.p.profile y
local notation "d"=> ((Tp).supportExponent)+1
local notation "C'" => Pane.cloak D' x
variable (D') (F: Income D' S x y hx (Burn.horizon q))
local notation "Λ"=>fun i:I=>i.self.paid
local notation "Γ"=>F.issue
include F
open RGComparison01
open Rosary.Repair
local notation "Tc"=>Aux.fare G LΩ
local notation "U0"=>Wheel.Ride.Pair.Note D' S x y hx (q:=q)
local notation "I0"=> Sigma (U0)
local notation "Ω₀"=>(Tc).stage U0
/- coarser actual beta post Budget. request model price height as function of kernel epoch -/
structure FrameNote (i:I0) where
    board : BudgetPoint
    same : VerifiedReset.Time.Same (Tp) board
    B : board.B=radiusB i.1
    thresh : board.threshold = Pressure.temp i.1
    post : ℝ
    pos : 0 < post
    earned : board.threshold^2*|post - Wheel.now (F.issue i.2.token) (κs+2) i.2.beta|≤ PostP.θ2 G (Tp) i.1 q
local notation "K0"=> FrameNote D' S x y hx F
local notation "Ω"=> (Ω₀).stage K0
local notation "V"=> Sigma (K0)
local notation "PP"=> fun i:V=> i.2.board
local notation "QM"=> fun i:V=> F.issue i.1.2.token
local notation "f★"=>fun i:V=> (i.1).1
local notation "B"=> fun i:V=> i.1.2.beta
local notation "BP"=> fun i:V=>i.2.post
local notation "cost"=> (Ω).Meter
local notation "T★"=> (fun i=> (PP i).threshold)
lemma coreHall : Wheel.Hall (Ω) (κs+2) (B) QM := by -- named explicit first? struct param
 let h := (Ω₀).liftF (Y:=V) Sigma.fst; obtain ⟨hT,hp,H⟩:= Wheel.Ride.Pair.lesson D' S x y hx F; exact ⟨hT.orbit _ _ h,fun i hi=> (hp i hi).pays _ h,h.tends.eventually H⟩
lemma stamped : Looks G (LΩ) (Ω) (f★):= Looks.high ( (Tc).liftF (Y:=Sigma (U0)) Sigma.fst) (Ω) (Sigma.fst (β:=K0)) ((Ω₀).liftF (Y:=V) _)
lemma warmth : cost T★ (-(1/2:ℝ)) := (Looks.bill (stamped D' S x y hx F) rate_old_temperature).eq_mem (Eventually.of_forall fun i=> i.2.thresh.symm)
lemma cold : cost (fun i=> (T★ i)⁻¹) (1/2:ℝ) := (Looks.bill (stamped D' S x y hx F) cost_inv).eq_mem (Eventually.of_forall fun i=> congr_arg _ i.2.thresh.symm)
lemma notice_β (he:p ≤ κs+1) : cost (discrepancy B BP QM (κs+2)) (graded (p+1)) := by
 let Q:=QM; let f(i:V):= BP i - Wheel.now (Q i) (κs+2) (B i)
 let b:=B; let H:= coreHall D' S x y hx F; have ht : cost (fun i=> (T★ i)^2*f i) (Burn.credit q):= by
    let L: Looks G LΩ Ω (f★):= stamped D' S x y hx F; have he' : cost (fun i=> PostP.θ2 G Tp (f★ i) q) (Burn.credit q):= (((Looks.bill (a:=Burn.credit q) L (thermometer _ _ (Burn.tracks G _))).lscale (VerifiedReset.Time.credit G Tp)).lscale 2); apply Meter.smaller he'; filter_upwards with i; rw [abs_mul, abs_of_nonneg (sq_nonneg (T★ i))]; exact i.2.earned.trans (le_abs_self _)
 let P(i:V):= T★ i; have hy: cost (fun i => discrepancy B BP QM (κs+2) i) (Burn.credit q):= by
    apply Meter.weak (Meter.eq_mem (Meter.mul (((cold D' S x y hx F).pow 2).mul (H.tune.stepI.pow 2)) ht) ?_) ?_; swap; · norm_num
    filter_upwards [H.tune.one] with i hi; change ((P i)⁻¹^2*gStep (b i)^2)*(P i^2*f i)=f i/b i; have hg:(P i) ≠ 0:= (PP i|>.threshold_pos).ne'; have hb:=Fare.gS _ hi|>.2; have hb': (b i)≠0:= hi.ne'; field_simp; linear_combination f i * hb
 apply hy.weak; unfold graded; rw [Burn.sale_eq]; have h':(p:ℝ) ≤ κs+1:=by exact_mod_cast he
 push_cast at * ; linarith
variable (a:ℝ)
omit F in
lemma humidP (x y j k:ℕ)(t a:ℝ){G:Gauge}{L:Side} : RGComparison01.Geo G L (fun i:ℝ=> Quipu.Sonnet.Vase.humid G x y j k (radiusB i) 1 t a):= by
 unfold Quipu.Sonnet.Vase.humid Quipu.Sonnet.Vase.basin; push_cast; exact ((((((Geo.fixed _).joins (Geo.basic Lantern.Bolt.size)).power _).times (Geo.fixed _)).times (Geo.fixed _)).times (Geo.fixed _))
-- radius and method
open Squall Calendars Calendars.Cove Quipu Sonnet Tern
variable (N : ℕ)
lemma atmosphere (j:ℕ) : cost (fun i=>Vase.humid G (PP i).power (PP i).order j N (PP i).B 1 (d) a) 0 := by
 let F0:=humidP (G:=G) (L:=LΩ) (Tp).power (Tp).order j N d a; refine (Looks.bill (stamped D' S x y hx F) F0.rate).eq_mem ?_; apply Eventually.of_forall; intro i; let H := i.2.same; dsimp only [Function.comp_apply]; rw [H.1,H.2.1, i.2.B]
local notation "Y"=>fun i:ℝ=> betaF G i (D'.L x)
variable (K ℓ p:ℕ)
local notation "p★"=>fun i:I=> price_ops (Moonset.raise (F.issue i)) p (p+ℓ) 1
noncomputable abbrev owes (A:I)(P:BudgetPoint)(z v:ℝ) := rent_gap (G:=G) P p N ℓ (gStep z) (gStep v) (price_ops (Moonset.raise (F.issue A)) p (p+ℓ) 1) ((X.p.profile y).supportExponent+1) a (F.issue A)
local notation "O"=> owes D' S x y hx F a N ℓ p
noncomputable def episode (G:Gauge)(L:Side)(K:ℕ)(x:ℝ) := ((K:ℝ)*(1+K* Calendars.Cove.caps (betaF G x L)))
local notation "I'"=> episode G LΩ K
omit F in
lemma episodes : Rate G LΩ 0 (I'):= Rate.mul_left ((Rate.const 1).add ((reserve_rate G LΩ).mul_left (K:ℝ))) _
lemma cost_gap (he:p ≤ κs+1) : cost (fun i:V=> episode G LΩ K (i.1.1)* O i.1.2.token i.2.board i.1.2.beta i.2.post) (graded (p+1)):=by
 let F0:= coreHall D' S x y hx F; let W:= (Ω); let X' i:=(Sigma.fst (β:=K0) i); let H:= stamped D' S x y hx F
 obtain ⟨Q,hQ,h⟩:= price_pool D' S x y hx F p ℓ
 have hS: cost (fun i:V=> price_ops (raise (QM i)) p (p+ℓ) 1) 0:= (Looks.bill H hQ.rate).smaller (Eventually.of_forall fun i=>(h (i.1.1) _ i.1.2.earns).trans (le_abs_self _))
 have hZ:= Moonset.books_charge F0 (by omega : p ≤ κs+2) (notice_β D' S x y hx F he) (Eventually.of_forall fun i=> i.2.pos) a G hS (warmth D' S x y hx F) (fun j (_:j ≤ p+ℓ)=> atmosphere D' S x y hx F a N j)
 exact ((Looks.bill H (episodes (D':=D') (x:=x) K)).mul hZ).weak (by simp)
-- expose feasible acquisition
structure Knowledge (η:ℝ)(v:ℝ) : Prop where
    stamp (A:I)(h:A.self.paid=strengthP (betaF G v LΩ)): 1+ price_ops (Moonset.raise (F.issue A)) p (p+ℓ) 1 ≤ caps (betaF G v LΩ)
    fee (i:U0 v) (P:FrameNote D' S x y hx F ⟨v,i⟩): episode G LΩ K v * O i.token P.board i.beta P.post ≤ Skull.tone G LΩ v η p -- Skull?
    forecast : RG.Stage.supportExponent Tp+1 ≤ a*radiusB v
    low : 0< v
variable (ha:0<a)
include ha
lemma acquired (h:p ≤ κs+1) (hη:0<η) : ∀ᶠ z:ℝ in atTop, PostDebt.Knowledge D' S x y hx F a N K ℓ p η z:= by
 let T:= Tc; have he:= cost_gap D' S x y hx F a N K ℓ p h; let zeta := Skull.platform η p
 have hf :∀ᶠ i in T.rail,∀ A:U0 i,∀ P: K0 ⟨i,A⟩,episode G LΩ K i* O A.token P.board A.beta P.post ≤ Skull.tone G LΩ i η p:= T.everybody _|>.mp ((Ω₀).everybody _|>.mp ((he zeta (by unfold zeta Skull.platform Skull.score; linarith)).mono fun i hi=>(le_abs_self _).trans hi))
 obtain ⟨Q,hQ,H⟩:= price_pool D' S x y hx F p ℓ; let Z:=d; filter_upwards [eventually_gt_atTop (0:ℝ), hf, Cove.stays ((RGComparison01.Geo.fixed 1).joins hQ), ((tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto).eventually_ge_atTop (Z/a))] with i h' hz hx he; exact ⟨fun A h=> (add_le_add_right ((le_abs_self _).trans (H i A h)) _).trans ((le_abs_self _).trans hx), hz,(by rw [mul_comm]; exact (div_le_iff₀ ha).mp he),h'⟩
end PostDebt
end YM.Qlocal.Moonset
