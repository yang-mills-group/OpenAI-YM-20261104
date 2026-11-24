import YM.FVA2.Facade.Landing
import YM.FVA2.Facade.Tracing
/-!
# Unmasked exponent on the multiscale hierarchy (for `Fk` linkage)

Same underlying data across expansion orders. Fix an assembly $L$, etc.; theorems
will apply on any such on this **finite inversion** torus. Here construct the rates
including the *actual* top Wilson action (keep its factor of 1/2) and all the
intermediate gauge choices and penalty costs. No performance claims (e.g. about
instance costs across periods, on a particular family of punctured charts or other test
locations). See `Arrival/Episodes.lean`: finite order evaluations can use one set
of sheets extending through that order (take enough for any external Laurent shifts).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic RGComparison.Core16
open PertExtension.Series Tested Radial Inherit
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {G: Gauge} {c f n:Side} {L:Fabric G n} {J:ChartRatio G}

 def rate (T:Cloth L) (i:L.Accounts) : Entry T→ℝ:= Option.elim i (firstBill ∘ line T) (fun k=> valve T k)
private lemma nn {n:Side}{L:Fabric G n}(T:Cloth L) (i:L.Cost)(x) : 0≤valve T i x:= by
 cases T with
 | floor=> exact Empty.elim i
 | @inLayer c f S b t hf L P C=> change Option L.Cost at i; cases i with
   | none=> exact mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg (fun _ _=> (G.price_range _).1))
   | some i=> exact nn C i _
termination_by structural T
private lemma vvnull {n:Side}{L:Fabric G n}(T:Cloth L) (i:L.Cost) : valve T i 0=0:= by
 cases T with
 | floor=> exact Empty.elim i
 | @inLayer c f S b t hf L P C=> change Option L.Cost at i; cases i with
   | none=>
       change substep (G:=G) P t (arrows (P:=P) (C:=C) (H:=b) (hf:=hf) (t:=t) 0)=0; rw [map_zero]; exact (subStill P t b).base0
   | some i=>
       change valve C i (descend (P:=P) (C:=C) (H:=b) (hf:=hf) (t:=t) 0)=0; rw [map_zero]; exact vvnull C i
termination_by structural T
variable (T:Cloth L)
-- retains top price; because Wilson full quotient rule sums with 1/2, penalties each orbit multiplicity exactly one.
lemma tasty (i:L.Accounts) : ContDiffAt ℝ ω (rate T i) 0:= by cases i with
                                      | none=> exact leaned (line T) firstGranted
                                      | some i=> exact valved T i
lemma rate_nn (i:L.Accounts)(x): 0≤ rate T i x:= by cases i with
                                      | none=> exact div_nonneg (Wilson.energy_nonneg _) zero_le_two
                                      | some i=> exact nn T i x
lemma uprightC (i:L.Accounts): Stationary (rate T i):= by
 apply Inherit.stable (tasty T i) ?_ (rate_nn T i); cases i with
 | some i=> exact vvnull T i
 | none=> change firstBill (line T 0)=0; rw [map_zero]; exact first_held.base0

variable (z:L.Accounts→PowerSeries ℝ)
 def headquarters := initialFull G n (z none)
local notation "Q"=> policy T (z ∘ some) (headquarters z)

lemma hotQ : (Q).P=(totalPrice (fun i=> Quadratic.genesis (z i) (rate T i))).P:= by
 apply records; intro x; change ((headquarters z).Q.flourish (line T x))+(unpaid T (z ∘ some)).flourish x=_; rw [bought,Fintype.sum_option]; unfold unpaid; rw [bought]; exact congr_arg₂ (·+·) (payments (line T) _ _ firstGranted x) rfl

variable (HJ:LocalRatio J)(hz:∀ i,0<term (z i) 0)(w:L.Accounts→ℝ→ℝ)(y:Flats G (Bottom L))
-- supplies all positive core and update claims on `drive`. Available regardless of whether performing final truss integration.
include hz HJ in
lemma collared : Commission J T (headquarters z) (z ∘ some):= released HJ (paidRoot T J z hz)
include hz in
lemma policyready : (core (Q)).RespectsPrice:= by
 -- keep J canonical (for the chart ratio).
 let J:= PertExtension.Orb.tray G; exact holding T (z∘some) _ J (collared T z (J:=J) (Orb.traySpec _) hz)

local notation "s"=> raise (rate T) w y
variable (hw:∀ i,ContDiffAt ℝ ω (w i) 0)(N:ℕ)(h:∀ i,Through N (amount (w i)) (z i))
private lemma jetMax {E:Type}[NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{V:E→ℝ}(hp:Stationary V)(hv:∀ x:E,0≤ V x)(x:E):0≤jet V 2 x:= by
 apply ge_of_tendsto (((directions hp.smooth x).shift (w:=2) (by
                        intro k hk; interval_cases k; exact (jet_zero V x).trans hp.base0; exact hp.base1 x)).tendsto_first)
 exact Filter.Eventually.of_forall (fun i=>mul_nonneg (sq_nonneg _) (hv _))
include hw h hz
lemma steep : Laplace.Steep (s) := by
 refine { steadies (rate T) w y (uprightC T) (tasty T) hw with
     gap := ?_ }
 apply quadratic_min; rintro ⟨r,x⟩ hx
 rw [initialQ (rate T) w y x (uprightC T) (tasty T) hw z N h r]; by_cases hr:r=0
 · subst r; rw [show flank y (0,x)=(x,0) from by simp [flank]]; unfold flourish; rw [← hotQ]; have he:0<(core (Q)).flourish x:= definite _ (policyready T z hz) x (fun i=> hx (by rw [i]; rfl)); exact add_pos_of_nonneg_of_pos (sq_nonneg _) (div_pos he zero_lt_two)
 · apply add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hr); apply div_nonneg _ zero_le_two; rw [bought]; exact Finset.sum_nonneg (fun i _=> by rw [Quadratic.native]; exact mul_nonneg zero_le_two (mul_nonneg (hz i).le (jetMax (uprightC T i) (rate_nn T i) _)))
omit hw h hz

local notation "π"=> ledge T (z ∘ some) J (headquarters z)
local notation "ω₀"=>jacobian J (U:=Warm T)
local notation "π₀"=> overhead J (Warm T)
local notation "μ"=> tangent G (Warm T)
local notation "Y"=> craving y Q (policyready T z hz) μ

include HJ
lemma assemble : layerFee (rate T) z ω₀= roll π₀ * π:= by
 let d:= roll (E:=Entry T) π₀; let V:= boost (line T) (chip (z none) firstBill); let D:= packed T (z ∘ some); let P:= LinearMap.fst ℝ (Panel T) (Flats G (Bottom L))
 have ht : boost P (Stack.rise ω₀)= d* boost P (tissue J (Warm T)):= by
     unfold tissue; rw [map_mul,boost_c, ← mul_assoc d]; change _= (roll π₀* roll ((π₀)⁻¹))* _; unfold roll; rw [← map_mul, ← map_mul,mul_inv_cancel₀ (official HJ).ne',map_one,map_one,one_mul]
 unfold layerFee; rw [Fintype.prod_option]; change chip (z none) (firstBill ∘ line T) * D*boost P (Stack.rise ω₀)= d*(V*(D* _)); rw [←pullPay (line T) _ firstBill firstGranted, ht]; unfold V d; ring

omit HJ in
private lemma upped (Q₂:Quadratic (Entry T))(q:(core Q₂).RespectsPrice)(b:Ticket (Entry T))(v:ℝ): uptake Q₂ μ q (roll v * b)= roll v * uptake Q₂ μ q b:= by
 apply PowerSeries.ext; intro i; unfold uptake; simp_rw [tagThrough, roll,coeff_C_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]; rw [tagThrough]; exact (integrateP Q₂ μ q).map_smul v _

 def constit (J:ChartRatio G)(V:Entry T→ℝ): PowerSeries ℝ:= PowerSeries.mk (Therm.stamp μ (coat y (jacobian J (U:=Warm T)) V) (s) 1)
-- name "s" notation can detach. Var check
 def overheadC (J:ChartRatio G): ℝ:= Y*overhead J (Warm T)
include hz
lemma high_pos : 0<overheadC T z hz y J:= mul_pos (craving_pos ..) (official HJ)

include hw h
lemma sloped (V:Entry T→ℝ)(hv:ContDiffAt ℝ ∞ V 0) : Through N (constit T w y J V)
   (C (overheadC T z hz y J) * Stack.read y (uptake Q μ (policyready T z hz) (π * Stack.rise V))):= by
 have he:= reading_stamp (rate T) w y (uprightC T) (tasty T) hw z N h ω₀ ((Ratio.jacobian_smooth HJ).of_le le_top) V hv Q (policyready T z hz) (hotQ T z) μ; rw [assemble T z HJ,mul_assoc (roll π₀), upped T,map_mul (Stack.read y),rollThrough,← mul_assoc,←map_mul] at he; exact he

-- Branch projection-independent in each orthant directions. unmarked money before division.
lemma sales (A:Ticket (Flats G n)) : Through N (constit T w y J 1) (C (overheadC T z hz y J)* Stack.read y (drive T (z ∘ some) (headquarters z) A J (collared T z HJ hz)).1.W):= by
 rw [←avowed T _ _ (collared T z HJ hz) HJ A]; have he:= sloped T z HJ hz w y hw N h 1 contDiffAt_const; rwa [rise_one,mul_one] at he

lemma entrance : 0<constantCoeff (constit T w y J 1):= by
 let q:=(policyready T z hz); have he: Through N (constit T w y J 1) (C (overheadC T z hz y J)*Stack.read y (uptake Q μ q π)):= by simpa only [rise_one,mul_one] using sloped T z HJ hz w y hw N h 1 contDiffAt_const
 have hQ:= high_pos T z HJ hz y; rw [← coeff_zero_eq_constantCoeff_apply, he 0 (by omega), coeff_C_mul,coeff_zero_eq_constantCoeff_apply, Warp.shape (Quadratic.upright Q μ q (reserve T (z ∘ some) _ J HJ (OpenSlots.restores (z none) _))),mul_one]; exact hQ

-- common canonical poly alignment for internal schedule. sufficient but not necessary
omit HJ h hw hz
lemma heated (i:L.Accounts) (N:ℕ) : ContDiffAt ℝ ω (fun t=> sheet z N t i) 0:= by unfold sheet Tested.peval Zone.eval; exact ContDiffAt.sum fun i hi=>(contDiffAt_id.pow _).smul contDiffAt_const
lemma traced_bare (i:L.Accounts)(N:ℕ): Through N (amount fun t=>sheet z N t i) (z i):= by
 let f:= fun t=>sheet z N t i; have he: amount f=shrink (z i) N:= by
   apply Tracks.seam _ (photo z N i) (EventuallyEq.refl _ _); unfold Tracks Facade.amount; rw [Stack.read_real,Tracks.asTerm]; simpa using! directions ((heated z i N).of_le le_top) 1
 change Through N (amount f) _; rw [he]; exact shrink_width _ _

end YM.FVA2.Facade
