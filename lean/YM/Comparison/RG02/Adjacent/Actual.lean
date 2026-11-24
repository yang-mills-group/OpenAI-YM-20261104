import YM.Comparison.RG02.Adjacent.Budget
import YM.Comparison.RG02.Step.History
/-!
# At the SAME next mesh on the Wilson history

Export costed `schedule` after reset, actual positive ratio, and coefficient/norm consumer:
combine `Debited.booking` (formal structural K,C budgets and β uncertainty still input)
with the `RealStep` exact comparison identities on the old frame. No comparison of
partition functions beyond those identities and denominator already proved.
The exact identities THEN use the kinetic readout `Caliber` of the caller, no hidden
coupling equality. Preserve further alignments and estimates, not asserting iteration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent.RealStep
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence LocalScript
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip}{P:PathData G}{O:ChartRatio G}
    (K:Bulk.Kernel S p P O) (F:Forest S.ratio)(w:S.Choices)
    (W:Bulk.Colors R G f)(x:fieldDir G c 1) (g:ℝ)
    (C:Caliber)(s:R.Mode)(r:ℕ)
open Actual
local notation "Σ'"=> ground K F w W r
lemma price_cover: exponentPrice (Bulk.Fk K F w W x r) g = (cover (ground K F w W r) r g x).re - (price K F w x).re := by
   unfold exponentPrice cover; rw [vpart]; simp_rw [ground,mul_add, sum_add_distrib, mul_ite,mul_zero,Finset.sum_ite_eq']; rw [if_pos (Finset.mem_range.mpr (by omega)),pow_zero,one_mul, Complex.add_re]; exact (add_sub_cancel_right _ _).symm
lemma hatch (b y:ℝ): office K F w g b x* Real.exp (exponentPrice (Bulk.Fk K F w W x r) g + y)= office K F w g b 0*Real.exp ((cover (ground K F w W r) r g x).re + y):= by
   let p:= Bulk.infrared S p P F w (K.b F); let u:= (cover (ground K F w W r) r g x).re
   have hx:= price_cover K F w W x g r; have hv : (price K F w x).re= -p x:= by simp only [price,Complex.neg_re,Complex.ofReal_re,p]
   have hz : p 0=0:= by
      have he:= Pole.price_zero K F w; exact Complex.ofReal_inj.mp ( show (p 0 :ℂ)= (↑(0:ℝ):ℂ) from by unfold price at he; simpa using he)
   rw [hx,hv]; unfold office standard calorie; rw [show Bulk.infrared S _ P F w (K.b F) 0=0 from hz];
   rw [sub_zero, mul_assoc (chartCost (K.covariance F w) g), mul_assoc (chartCost (K.covariance F w) g), mul_assoc (tab (F:=F) (O:=O)*_),mul_assoc (tab (F:=F) (O:=O)*_),← Real.exp_add,← Real.exp_add]; congr 3; ring -- likely needs explicit abel

variable (U:Family G)(Y:Bulk.Chain U.path) (N m q:ℕ)(hU:U.Makes) (h:m<N)
local notation "g'"=> Pert.Asymptotics.regulatorRun U N q m
local notation "t"=> Pert.Asymptotics.regulatorRun U N q (m+1)
local notation "ρ"=> (U.path.rep N q (m+1))
local notation "ρ'"=> (U.path.rep N q m)
local notation "K" => (Y.step N m q h)
local notation "A"=> U.path.levels.clock.op m q
abbrev convention := t/g' -- hope t macro works
local notation "L"=> convention U N m q
include hU h
open YM.Comparison.RG02.Local.RealStep (trajectory coupling_pos)
lemma convention_paid: 0< convention U N m q := div_pos (coupling_pos U N q _ hU h) (coupling_pos U N q _ hU h.le)
lemma convention_confirm: t/(convention U N m q)=g' := by unfold convention; field_simp [ (coupling_pos U N q _ hU h).ne', (coupling_pos U N q _ hU h.le).ne']
lemma factor: g'*L=t := by unfold convention; exact mul_div_cancel₀ _ ((coupling_pos U N q m hU h.le).ne') -- order
lemma core_weight:
   |(convention U N m q)^2 - C.tariff r (Pert.Asymptotics.regulatorRun U N q (m+1))|= t^2*|(U.path.rep N q m).beta-(U.path.rep N q (m+1)).beta*C.tariff r (Pert.Asymptotics.regulatorRun U N q (m+1))| := by
   rw [← trajectory U N q m hU h.le, ← trajectory U N q _ hU h,← abs_of_nonneg (sq_nonneg t),← abs_mul]
   unfold convention temperature;
   congr 1; field_simp [(coupling_pos U N q _ hU h).ne', (coupling_pos U N q _ hU h.le).ne']

variable (d:V→ℤ) (F:Forest (U.path.levels.clock.op m q).ratio) (w:(U.path.levels.clock.op m q).Choices)
   (W : Bulk.Colors R G (U.side (m+1) q))
   (x:fieldDir G (U.side m q) 1)
   (Z : Lit R (Config G (U.side (m+1) q)))
local notation "V'"=> sample g' x
local notation "M"=> (ground K F w W r)
local notation "Ψ" P => born P (C.back r)

-- real payoff. S is same mesh dictionary. Use after obtaining Y at Flora/construct.
def cost (p:Display (fieldDir G (U.side m q) 1))(d:ℤ):= cover (born p (C.back r) d r) r (Pert.Asymptotics.regulatorRun U N q m)- ages p d r g' (convention U N m q)
lemma price_scale: sample t ((L)⁻¹ • x)= sample g' x := by rw [Integral.sample,smul_smul, ← div_eq_mul_inv, convention_confirm U N m q hU h]; rfl
section price
-- cost of deciding to implement C at THIS cutoff coupling. Does not bound structural persistence costs.
variable (T':Display (fieldDir G (U.side m q) 1)) (a:ℕ→ℤ)(j:ℤ)(Δ:ℝ)
    (ha : Charge r a T')(hv : Monotone a)
    (he : abs ((U.path.rep N q m).beta-(U.path.rep N q (m+1)).beta*C.tariff r (YM.Pert.Asymptotics.regulatorRun U N q (m+1))) ≤ Δ)
    (hu :∀i≤r,∀k≤(a i).toNat, 0≤(Receipts.root (Receipts.verdict C r (j+i-k) (r-i)) (YM.Pert.Asymptotics.regulatorRun U N q (m+1))).re)
include hv ha he hu
lemma turns_accepted (q' : ℕ)(v : Fin q' → fieldDir G (U.side m q) 1):
   ‖iteratedFDeriv ℝ q' (cost C r U N m q T' j) x v‖ ≤ ∑ i∈range (r+1), ∑ k∈range ((a i).toNat+1), Debited.debit C r j (convention U N m q) (YM.Pert.Asymptotics.regulatorRun U N q (m+1)) Δ i k * ‖iteratedFDeriv ℝ q' (Assembly.jet (born T' (C.back r) j r i) k) x v‖ := by
     have hh := Debited.booking C r j (convention U N m q) (YM.Pert.Asymptotics.regulatorRun U N q (m+1)) ha hv (convention_paid U N m q hU h) (coupling_pos U N q _ hU h).le Δ (by rw [core_weight C r U N m q hU h]; exact mul_le_mul_of_nonneg_left he (sq_nonneg _)) hu x q' v
     rwa [convention_confirm U N m q hU h] at hh
end price

include Y
section Wheel
variable (B : (U.path.levels.clock.op m q).Choices → Set (F.Slice G)) (hs:∀v, MeasurableSet (B v)) (wA: ∀v', B v'⊆zone (Y.step N m q h) (U.path.rep N q (m+1)).p F (Pert.Asymptotics.regulatorRun U N q (m+1)) ((convention U N m q)⁻¹ • x))
  (hZ:Actual.Floor (U.path.rep N q (m+1)) Z)(hp:Bulk.Well W)
open YM.Comparison.RG02.Local.RealStep (genuine)
local notation "E"=> Local.vacuumError (U.path.rep N q (m+1)) Z K t F w W B ((convention U N m q)⁻¹ • x) r
local notation "δ"=> dilation R (Trade.mark d (convention U N m q))
include hs wA hZ hp
lemma schedule : (U.path.rep N q m).eval (sample g' x)= office K F w t (levelScalar ρ) 0 * Real.exp ((cover (born M (C.back r) 0 r) r g' x).re + E-(cost C r U N m q M 0 x).re) := by
   let B':= genuine U N q m Y h Z W F w ((convention U N m q)⁻¹ • x) hU hZ hp r (Fintype.card V) (fun j=>Finset.card_le_univ _) B hs wA
   rw [← price_scale U N m q hU h x, B'.1,hatch]
   simp only [cost,Pi.sub_apply, ages,zpow_zero, Complex.ofReal_one,one_mul, factor U N m q hU h, Complex.sub_re]; congr 2; ring
omit hs wA hZ hp [Fintype V] Y in
private lemma remaining (k:Finset V) : ∏ i∈k, Trade.mark d (L) i=(↑((L)^(∑ i∈k,d i)):ℂ):= by -- reuse? Barter.remaining private
   induction k using Finset.induction with
   | empty=> simp
   | insert s k he ih => rw [Finset.prod_insert he,Finset.sum_insert he,zpow_add₀ (convention_paid U N m q hU h |>.ne'), ih,Complex.ofReal_mul]; rfl
variable (n:ℕ)(H' :∀j:R.Mode,j.val.card≤ n)
local notation "d₀"=> Trade.markDebt d s
local notation "H"=> words K F w W r s
local notation "ε"=> Local.markingError ρ Z K t F w W B ((convention U N m q)⁻¹ • x) r n
include H'
lemma earned : ((dilation R (Trade.mark d (L)) (Local.cumulant ρ Z A V'))).part s= cover (born H (C.back r) (Trade.markDebt d s) r) r g' x + (δ ε).part s - cost C r U N m q H (Trade.markDebt d s) x := by
   let B':= genuine U N q m Y h Z W F w ((convention U N m q)⁻¹ • x) hU hZ hp r n H' B hs wA
   rw [← price_scale U N m q hU h x, B'.2.2.1,map_add,Poly.part_plus, dilation_part]; have he:(Order.value (t:ℂ) (logMarked (Bulk.Fk K F w W ((convention U N m q)⁻¹ • x) r))).part s=cover H r t ((convention U N m q)⁻¹ • x):= by rw [vpart]; rfl
   simp only [cost,Pi.sub_apply,ages]; rw [factor U N m q hU h, remaining U N m q hU h d, he]; unfold Trade.markDebt; abel
end Wheel
end YM.Comparison.RG02.Adjacent.RealStep
