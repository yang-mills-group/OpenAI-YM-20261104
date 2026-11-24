import YM.FVA2.Arrival.Runtime
import YM.XSpace.Photo
/-!
# Connected and full comparisons of predeclared $B^a$ columns

The finite-regulator comparison cost, expressed with `ApplyMF`, before reorganizing in the
matrix notation of `Dframe`. `entries`, `Uniform`, `maturity`. Keep any fixed compact separated
profile set. Take any large enough mesh along `Front`; estimate applies **before** taking the
separated-test Riemann sums, on all common-center choices passing those placement criteria. Here
`whereKnown` also provides smearing convergence (requires the test-budget, not estimating powers
of spacing for that convergence yet). This is on the **matched** columns (don't try to deduce
these estimates by multiplying errors on *unmatched* columns by the field-change matrices).

`high_application` for constructing this setup for all profiles (use `G.Simple` and the indicated MS Data
and conventions -- `μ` here is logarithmic). This uses concrete inputs, includes
even the connected sector (`coherentF` applied), and includes estimates on the continuum
comparisons with them (`book`, `tour`). See `Voice/Encore.lean` (exports both comparisons at the
MS supplied endpoints, and with `W` compensation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival.Landing
open Function Filter Set Finset Metric MeasureTheory Real Lattice Wilson
open MS MS.Local.Physical MS.Tide MS.Tide.PeakT MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus Press Change Schedule
open scoped Topology ContDiff Classical
variable {n:ℕ} {G:Gauge} {W:Type}
variable (μ:ℝ) (Y:XSpace.Initialize G) {K: Land.Booked (Press.portDeck G)} (S:MS_Data G K) (M:Land.Prescription (Press.portDeck G))
variable (u:Fin n→Label (Press.portDeck G))(t:Finset (Fin n))(k:ℕ)
local notation "Z"=> (XSpace.Cirrus.Sample n)
local notation "H"=> entries μ Y u M t k
local notation "P"=> ( showR (n:=n) μ )

def moondye (x:Points n):ℂ:= tour S u μ (plot x) t k
local notation "T"=> moondye μ S u t k
variable (h:G.Simple)(hp:TaylorOKF S (Press.wickInput Y) M)
theorem fresh : ContinuousOn ( moondye μ S u t k ) (conf n):= fun _ hx=> ContinuousAt.continuousWithinAt (( Dial.contin S u _ (track hx) t k μ ).1.comp plot_exposes.continuousAt)
theorem centers : XSpace.Cirrus.Centered ( entries μ Y u M t k ):= fun _ _ _=> rfl
include h hp
lemma maturity : Senses (conf n) ( entries μ Y u M t k ) (moondye μ S u t k):= by
 intro x hx; have hu : Tendsto (H-T ∘ XSpace.Cirrus.familiar) (Gate x) (𝓝 0):= PeakT.topos mild_p ( speed x ) ( Schedule.rate μ x hx Y u S M t k h hp ); obtain he:= ( hu.add ((( Dial.contin S u (plot x) (track hx) t k μ ).1.comp plot_exposes.continuousAt).tendsto.comp (senseG x) : Tendsto ( _ ∘ _ ) (Gate x) (𝓝 (T x))) ); exact (by simpa only [zero_add,sub_add_cancel] using! (show Tendsto (H-T ∘ XSpace.Cirrus.familiar+T ∘ XSpace.Cirrus.familiar) (Gate x) (𝓝 (0+T x)) from he))
structure Uniform (A:Set (Points n)): Prop where
 points : ∃ C:ℝ,0<C∧∀ᶠ m in Front,∀ i:Z,grab i=m→welcome i→familiar i ∈ A→ ‖H i-T (familiar i)‖≤ C * i.F.spacing^mildG
 test (e:ℝ) : 0<e→ ∀ᶠ m in Front,∀ f:Test n, tsupport f ⊆ A →∀ b:ℝ,XSpace.TestBudget.Bound f b → ‖ Deposit m H f-f.applyTo T‖ ≤ b*e
lemma adj_uniform (A:Set (Points n))(ht:IsCompact A)(he:A⊆ conf n): Uniform μ Y S M u t k A:= by
 refine ⟨ ?_, fun i hi=> graduate H T (conf_open n) (fresh μ S u t k) he ht ( maturity μ Y S M u t k h hp ) (centers μ Y M u t k) i hi ⟩
 choose c hc hC using fun x:A=> ( Schedule.rate μ x.val (he x.property) Y u S M t k h hp );
 choose r hr hs using fun x:A=> gate_senses _ (hC x); let B(x:A):=ball x.val (r x); obtain ⟨s,Hx⟩:= ht.elim_finite_subcover B (fun _=> isOpen_ball) (fun y hy=> mem_iUnion.mpr ⟨⟨y,hy⟩, mem_ball_self (hr ⟨y,hy⟩) ⟩); let u0:= ∑ i∈s,c i; have hu : 0≤u0:= Finset.sum_nonneg fun i _=> (hc i).le
 refine ⟨1+u0,by positivity,?_⟩; filter_upwards [frontier.smaller,(eventually_all_finset s).mpr (fun x _=> hs x)] with m hm Hp i hi hy hx; obtain ⟨j,hj⟩:= mem_iUnion.mp (Hx hx); obtain ⟨p,hp⟩:= mem_iUnion.mp hj
 subst m; apply le_trans (Hp j p i.layout i.center hy hp); unfold Tide.lake; rw [show exp (-mildG*(P).profile.θ i)= i.F.spacing ^ mildG from ?_]; swap
 · rw [show (P).profile.θ i= -Real.log _ from theta_value hm]; rw [ Real.rpow_def_of_pos i.F.positive ]; congr 1; ring
 refine mul_le_mul_of_nonneg_right ( le_trans (Finset.single_le_sum (f:=c) (fun i _=> (hc i).le) p) (by linarith) ) (Real.rpow_nonneg i.F.positive.le _)
lemma runs (L:XSpace.Run)(x:Points n)(hx:x∈conf n) : Tendsto (fun i:ℕ=> entries μ Y u M t k (ascend x (L.step i))) atTop (𝓝 (moondye μ S u t k x)):= (maturity μ Y S M u t k h hp x hx).comp ((points_at x).comp (goesFront ( XSpace.Expense.Stretched.runs L )))

open PeakT (ordZ)
omit hp h -- existence outputs at any index set
-- `Trial` estimate with quantities budgeted for all allowed fields. Later use even
-- with an actual `Run`.
structure Lifetime (M:Land.Prescription (Press.portDeck G)):Prop where
 plan : TaylorOKF S (Press.wickInput Y) M
 purposes (v:ℝ)(W I:Type)[LinearOrder W] (c:W→Label (Press.portDeck G)) (L:Filter I)(p:Trial I W) (_hp:Uses p L v):
    ∃! f:Terrify W I, coherentF K S ( wickInput Y ) c p v true M L f ∧ ∀ i s,bury i s f= Top.value Y c M (p.head i) (fun w=>p.off w i) ( dimT p.side i ) ( v-p.profile.θ i ) s
 whereKnown (v:ℝ)(n:ℕ) (c:Fin n→Label (Press.portDeck G)) (t:Finset (Fin n)) (k:ℕ) (A:Set (Points n)) : IsCompact A→ A ⊆ conf n → Uniform v Y S M c t k A
include hp h
lemma life : Lifetime Y S M:= by
 refine ⟨hp, ?_,fun v n t u k A hA ht=> adj_uniform v Y S M t u k h hp A hA ht⟩; intro v W I l c L p he; obtain ⟨V,hz⟩:= Dial.check_tF S ( wickInput Y ) c p hp he h true; exact ⟨ V,⟨hz,fun i s=> (Top.identifies Y c M ( p.head i ) _ ( dimT p.side i ) _ s (⟨( p.side i ).val,two_mul (α:=ℕ) _⟩)).1 ( hz.cost i s )⟩,fun y hy=> Dial.separateF _ _ _ hy.1.cost hz.cost hy.1.init hz.init⟩
-- use same team as original raw PS application if desired even after W; also high Taylor witness independent of parity/horiz cost choice
open MS.Wind MS.Wind.Leading MS.Native MS.Outlook MS.High MS.Mach MS.Motif
omit hp in
lemma at_team {a:Land.Prescription (Press.portDeck G)}(ha: TaylorOK S ( Press.program Y ) a) : ∃ M: Land.Prescription (portDeck G), M.team = a.team ∧ Lifetime Y S M:= by
 have hc d (i:Land.Plaid (portDeck G) d):= physicalAtF ( wickInput Y ) (j:=Land.read i) h ha.bulk ( fieldD S.bulkOK (S.markOK d i) wisdom (( K.law d i).moodQ)) (initialHF (K.law d i) ( Land.sizeG i ) ( S.markOK d i ))
 choose p H' hP using hc; exact ⟨ ⟨ a.team,p,H'⟩,rfl, life Y S _ h ⟨ ha.bulk,hP ⟩⟩ -- H syntax
omit hp in
lemma high_application : ∃ M,Lifetime Y S M:= by obtain ⟨M,H'⟩:= High_stopsF h S ( wickInput Y ); exact ⟨M,life Y S M h H'⟩
end YM.FVA2.Arrival.Landing
