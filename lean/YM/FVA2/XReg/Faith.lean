import YM.FVA2.XReg.Token
/-!
# The X scheme after applying the position-coupling measurement

The same (X position) scheme and arrays at the given `ν`, including the pointwise multilinear
operators here (`rate` based on `meteor`) and the whole smearing after this
transformation. Proves convergence of the independent Wilson arrays in that coupling;
see `confidence`, `tents`, `points`, `written`. Still before the mass-independent
N adjustment in `Scale`. A result for formal coefficients, not an asymptotic
assertion from a nonperturbative theory.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Faith
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Pivot CoverTest Higher State Choice Token
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(S: Prescription (Press.portDeck G)){O:Booked (Press.portDeck G)} (T: MS_Data G O)
local notation "φ"=> conversion ν K T
local notation "θ"=> choice ν K T
local notation "L"=> chooseL ν V T d
local notation "F"=> Token.leaf_t ν K T d
open Rose
-- retain Cp4 f(T) independent of book gauge.Native continuity.Report.Subject.
structure Lit (z:Cn): Prop where
   cost : Token.Payment ( Choice.choice ν K T ) z
   trueQ : CoreR z
   slope : coeff 1 z=1
variable (a: XSpace.Cirrus.Sample n) (p:Tags G d n)
variable (h:G.Simple)(hs: TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hv: Ace.UnitP S)
include h hs hr hv
lemma hearty : Lit ν K T ( conversion ν K T ):= by obtain he:= Choice.stance ν Y K S T h hs hr hv; have ht:= covers θ (proper ν K T) he; exact ⟨ ht, Token.core_l _ ht ( Choice.token ν Y K S T h hs hr hv ), Token.stamp_t _ (proper ν K T) he⟩
lemma uniquet {z:Cn}(H:(Choice.choice ν K T).subst z=X)(H':Rooted z): z= conversion ν K T:= Token.paid φ ( both ( hearty ν Y K S T h hs hr hv ).cost) H H'
lemma canonical : Formal ( Token.leaf_t ν K T d ) ∧ constantCoeff (Token.leaf_t ν K T d)=1:= by
    obtain H:= hearty ν Y K S T h hs hr hv; unfold Token.leaf_t; have hz: constantCoeff ( stepV φ L )=1:= by rw [ stepV,← coeff_zero_eq_constantCoeff_apply, coeff_mk,pay0,coeff_zero_eq_constantCoeff_apply, baseL ];
    exact ⟨ ⟨⟨ _, Unique.fees H.trueQ _⟩, (isUnit_iff_constantCoeff («φ»:= stepV φ L)).2 (by rw [hz]; exact isUnit_one) ⟩, hz ⟩
-- measured equality still no N. f and L canonical above.
omit h hs hr hv
abbrev rate (d:ℕ)(x:Points n) := status ( Token.leaf_t ν K T d ) ( substitute φ (meteor ν T d x) )
abbrev reports (d:ℕ): Reports G d := realm (Token.leaf_t ν K T d) ( substitute φ ( State.kernel ν T d ) )
include h hs hr hv
lemma rate_era (x:Points n) : rate ν K T d x=substitute φ (wall ν V T d x):= resetP φ L _ (hearty ν Y K S T h hs hr hv).cost.own
lemma reports_use : reports ν K T d=substitute φ (State.author ν V T d):= resetR φ L _ (hearty ν Y K S T h hs hr hv).cost.own
lemma report_price (t:Test n): reports ν K T d k n t p= t.applyTo (fun x=> rate ν K T d x k p):= by
    rw [ reports_use ν Y K S T h hs hr hv, ← Point.seenT ]; simp_rw [rate_era ν Y K S T h hs hr hv,Dframe.translate,rules,smul_eq_mul,exact_trace, Test.applyTo,Finset.mul_sum ]; rw [integral_finsetSum]; · apply Finset.sum_congr rfl; intro i _; rw [ ← integral_const_mul ]; refine integral_congr_ae (Eventually.of_forall (fun x=>?_ )); ring
    intro i _; exact ( t.smearing ( show ContinuousOn _ _ from (continuousOn_const (c:=Program.cut φ i k) ).mul ( State.road ν V T p i ) )) -- smearing g := const*a.
omit h hs hr hv
lemma Rosa : Point.story ( Rose.measureₓ Y K d a ) p= PowerSeries.subst ( Rose.χ Y K a.F ) (Point.story (Rose.cooked Y V d a) p):= by refine PowerSeries.ext fun j=>?_ ; rw [Point.story,coeff_mk,Rose.measure_paid,Rose.turn_coins ]
local notation "𝕍"=> cooked Y V d a
lemma recompose (hm:Use Y K a.F): PowerSeries.subst (prospects ν Y K S a.F) (Point.story (measureₓ Y K d a) p)= PowerSeries.subst ( Dframe.reset ν S a.F ) (Point.story ( Rose.cooked Y V d a ) p):= by
    let t:= Dframe.reset ν S a.F; let P:= Point.story 𝕍 p; let H:= Rose.χ Y K a.F; let y:=chosen Y K a.F; rw [ Rosa ];
    change PowerSeries.subst ( PowerSeries.subst t y ) (P.subst H)= _; have hy:= cert ( zero_choice Y K a.F ); rw [ ← subst_comp_subst_apply ( licence y hy ) ( licence t ( share .. ) ), subst_comp_subst_apply ( licence H ( cert ( Rose.χzero .. ) ) ) ( licence y hy ), show H.subst y=X from χverts Y K a.F hm,X_subst ]
abbrev Touch (ν:ℝ){V: Store G}(K:Rose.Pick V){O:Booked (Press.portDeck G)}(T: MS_Data G O)(x:Points n)(p:Tags G d n) := Point.story (rate ν K T d x) p
-- asympt diagonal path all Profile.P
include h hs hr hv
theorem center {x:Points n}(hx:x∈conf n) : Harmony (Gate x) (fun i=> Point.story ( Rose.measureₓ Y K d i ) p) (Touch ν K T x p):= by
    let f(i:Sample n):= prospects ν Y K S i.F; have hp:= hearty ν Y K S T h hs hr hv;
    apply Token.earn (q:=θ) _ _ (proper ν K T) (Choice.stance ν Y K S T h hs hr hv ▸ one_ne_zero) (Q:=f) ( Eventually.of_forall fun i=> g0 .. ) ( fun i=> (forecast ν Y K S T h hs hr hv i).comp (liftG x) ); -- convert eventually
    have he : (Touch ν K T x p).subst θ = Point.story ( wall ν V T d x ) p:= by unfold Touch; rw [rate_era ν Y K S T h hs hr hv,moves _ _ hp.cost.own, subst_comp_subst_apply ( licence φ hp.cost.own ) ( licence θ (proper ν K T)),hp.cost.left, X_subst]
    intro k; rw [ he ]; unfold Point.story; rw [coeff_mk]; apply ( State.moveT ν Y V S T h hs hr hv p k x hx ).congr'; filter_upwards [(liftG x).eventually (usable Y K h)] with a ha; rw [recompose ν Y K S a p ha]; rw [ ← moves ( Rose.cooked Y V d a ) p (share ..),Point.story, PowerSeries.coeff_mk ] -- issue Point.story unfold lhs.He hi Angle
lemma confidence (k:ℕ): Senses (conf n) (fun i=> Rose.measureₓ Y K d i k p) (fun x=> rate ν K T d x k p):= by intro x hx; obtain H:= center ν Y K S T p h hs hr hv hx k; simpa only [Touch, Point.story, coeff_mk] using H
lemma tents : HasAll Front (fun i=> Rose.proposed Y K i d ) ( reports ν K T d ):= by
    intro k n t p; simp_rw [ Rose.represents Y K _ ]; rw [report_price ν Y K S T p h hs hr hv]; exact Photo.sees_test (conf n) t _ (conf_open _) (confidence ν Y K S T p h hs hr hv k) (fun _ _ _=>rfl) t.tsupport_subset
-- estimates after normalization only epsilon. (rate of power may not asserted through all higher). Quant in test & point separately. Arity fixed.Profile power-coupling independent.Unit.
variable (U:Set (Points n))(hc:IsCompact U)(hq:U⊆ conf n)
include hc hq
lemma points (k:ℕ): Accurate U (fun i=> Rose.measureₓ Y K d i k p) (fun x=> rate ν K T d x k p):= ( confidence ν Y K S T p h hs hr hv k ).placed hc hq
lemma written (k:ℕ) (v:ℝ) (he:0<v): ∀ᶠ i in Front,∀ f:Test n,tsupport f⊆ U →∀ b:ℝ, TestBudget.Bound f b→ ‖Rose.proposed Y K i d k n f p- reports ν K T d k n f p‖≤ b*v:= by
    have hz:= confidence ν Y K S T p h hs hr hv k; simp_rw [Rose.represents, report_price ν Y K S T p h hs hr hv]; exact graduate _ _ (conf_open _) hz.priced hq hc hz (fun _ _ _=>rfl) _ he
end YM.FVA2.Reg.Faith
