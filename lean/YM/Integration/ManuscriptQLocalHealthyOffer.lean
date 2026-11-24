import YM.Integration.WilsonCurvatureRankRate
import YM.Integration.NativeWilsonTaggedRemainder
import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.ManuscriptQLocalPacketFootprint
import YM.Integration.ActualWilsonPacketGerms
import YM.Integration.QLocalInheritedMarkedVariation
import YM.Integration.LocalComparisonReadout
import YM.MergeProof.TeamFlow
import YM.MergeProof.Plaza

/-! Original mixed kernel estimates in coupling units for Lemma qlocal.
The exponential root invoice applies to the coefficient when the explicit
coupling prefactor is one. All marked inputs above a requested total grade
then have the requested signed Wilson first-moment estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalKernelTariff
open Filter Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
  {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
  {p : BudgetPoint} {L : V → Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V → ℝ} {g width budget : ℝ} {a b : ℕ}

theorem unchanged (H : P.Paid p L region w g width budget a b) (zero : ∀ i,P.power i=0) (t : ℝ) :
    P.Paid p L region w t width budget a b := by
  refine { H with roots := fun v => ?_ }
  simpa only [zero,zpow_zero,norm_one] using H.roots v

/-- Unlike the prefactor, the native norm of each token and its full
exponential path bill are charged at coupling one on the same original bank. -/
def bare (v : V) (i : ℕ) : ℝ :=
  if v∈(P.mode i).val then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i)*T.coin*Real.exp (width*T.fall)
  else 0

theorem quoted (H : P.Paid p L region w 1 width budget a b) (v : V) :
    SumBudget (bare (w:=w) (width:=width) P v) budget := by
  convert (H.roots v) using 1
  funext i
  by_cases h:v∈(P.mode i).val
  · cases hp:P.packet i <;> simp [ManuscriptQLocalKernelTariff.bare,h,hp]
  · simp [ManuscriptQLocalKernelTariff.bare,h]

def charged (μ : Measure (Config G n)) (g : ℝ) (x : IndependentTests D) (v : V) (r i : ℕ) : ℝ :=
  if v∈(P.mode i).val ∧ (r:ℤ)≤P.power i + (P.rank i:ℤ) then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i)*Real.exp (width*T.fall)*
        ∫ U,‖P.term (testInclusion D x) g U i‖ ∂μ
  else 0

/-- The physical response of every row above the specified total grade,
including arbitrary signed Laurent prefactors and the unweighted marked rank zero. -/
theorem graded (H : P.Paid p L region w 1 width budget a b)
    (μ : Measure (Config G n)) (x : IndependentTests D) (v : V) (r : ℕ)
    (g η C : ℝ) (hg : 0<g) (h1 : g≤1) (hC : 0≤C)
    (terms : ∀ i T,P.packet i=some T →
      (∫ U,‖T.read (testInclusion D x) U‖ ∂μ) ≤ T.coin*(C*g^((P.rank i:ℝ)-η))) :
    SumBudget (charged (w:=w) (width:=width) P μ g x v r) (C*g^((r:ℝ)-η)*budget) := by
  apply budget_mono (budget_scale (mul_nonneg hC (Real.rpow_nonneg hg.le _)) (quoted P H v))
  · intro i
    unfold charged
    split
    · cases hi : P.packet i with
      | none => exact le_rfl
      | some T =>
        exact mul_nonneg (mul_nonneg (Poly.worth H.positive _).le (Real.exp_pos _).le)
          (integral_nonneg fun _=>norm_nonneg _)
    · exact le_rfl
  · intro i
    have base := (quoted P H v).1 i
    by_cases h : v∈(P.mode i).val ∧ (r:ℤ)≤P.power i + (P.rank i:ℤ)
    · cases hi : P.packet i with
      | none => simp [charged,bare,h,hi]
      | some T =>
        have expo : (r:ℝ)-η≤(P.power i:ℝ)+(P.rank i:ℝ)-η := by
          apply sub_le_sub_right
          exact_mod_cast h.2
        have hpowers : ‖(g:ℂ)^P.power i‖ * g^((P.rank i:ℝ)-η)≤g^((r:ℝ)-η) := by
          rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hg.le,←Real.rpow_intCast,
            ←Real.rpow_add hg]
          apply Real.rpow_le_rpow_of_exponent_ge hg h1
          linarith
        simp only [bare,charged,h,if_true,hi,MarkedPackets.term,norm_mul,integral_const_mul]
        calc
          _ ≤ Poly.toll w (P.mode i)*Real.exp (width*T.fall)*
              (‖(g:ℂ)^P.power i‖*(T.coin*(C*g^((P.rank i:ℝ)-η)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (terms i T hi) (norm_nonneg _))
              (mul_nonneg (Poly.worth H.positive _).le (Real.exp_pos _).le)
          _ = Poly.toll w (P.mode i)*T.coin*Real.exp (width*T.fall)*C*
              (‖(g:ℂ)^P.power i‖*g^((P.rank i:ℝ)-η)) := by ring
          _ ≤ _ := (mul_le_mul_of_nonneg_left hpowers (mul_nonneg (mul_nonneg
              (mul_nonneg (Poly.worth H.positive _).le (H.coefficient i T hi).1)
                (Real.exp_pos _).le) hC)).trans_eq (by ring)
    · simpa only [charged,if_neg h] using mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hg.le _)) base

def cap (k : ℕ) : ℝ := (2:ℝ)^k*(1+2^k*(k:ℝ))

theorem climate (A : Levels G) (hG : G.Simple) (k : ℕ) {η : ℝ} (hη : 0<η) (hη₁ : η<1) :
    ∀ᶠ m : ℕ in atTop, ∀ (g : ℝ),0<g → g≤1 → A.clock.hatCoupling m≤2*g →
      ∀ q≤k,(cool A m)^q+2^q*((q:ℝ)*vanishP A m) ≤ cap k*g^((q:ℝ)-η) := by
  have all := (Filter.eventually_all_finset (Finset.range (k+1))).mpr (fun q _=>
    WilsonCurvatureRankRate.thermal A hG q (s:=(q:ℝ)-η) (by linarith))
  filter_upwards [all] with m h
  intro g hg hg₁ hhat q hq
  have herr := h q (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  have hq2 := pow_le_pow_right₀ (show 1≤(2:ℝ) by norm_num) hq
  have hcap : 1≤cap k := by
    unfold cap
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by norm_num)
    · exact le_add_of_nonneg_right (by positivity)
  by_cases hz : q=0
  · subst q
    simpa only [pow_zero,Nat.cast_zero,zero_mul,mul_zero,add_zero,zero_sub] using
      one_le_mul_of_one_le_of_one_le hcap
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg hg₁ (neg_nonpos.mpr hη.le))
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hs : 0 ≤ (q:ℝ)-η := by linarith
  have hhat₀ : 0≤A.clock.hatCoupling m := by unfold Calendar.hatCoupling; positivity
  have hpow : (A.clock.hatCoupling m)^((q:ℝ)-η) ≤ (2:ℝ)^k*g^((q:ℝ)-η) := by
    apply (Real.rpow_le_rpow hhat₀ hhat hs).trans
    rw [Real.mul_rpow (by norm_num) hg.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hg.le _)
    apply le_trans _ hq2
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have positive := Real.rpow_nonneg hhat₀ ((q:ℝ)-η)
  have hq' : (q:ℝ)≤k := by exact_mod_cast hq
  calc
    _ ≤ (1+(2:ℝ)^k*(k:ℝ))*(A.clock.hatCoupling m)^((q:ℝ)-η) := by
      rw [add_mul,one_mul,mul_assoc]
      exact add_le_add herr.2.1 (mul_le_mul hq2 (mul_le_mul hq' herr.2.2
        (Real.exp_pos _).le (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg q) (Real.exp_pos _).le) (pow_nonneg (by norm_num) k))
    _ ≤ _ := (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by unfold cap; ring)

theorem small {C : Family G} (hC : C.Makes) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ,m≤N → Pert.Asymptotics.regulatorRun C N p m≤1 := by
  filter_upwards [(Next.Rank.Station.hat_rate C.path.levels hG).eventually_ge_atTop (4:ℝ)] with m h
  intro N p hm
  apply (IterationFour.Currency.hat_g hC N p m hm).2.trans
  let u := C.path.levels.clock.hatBeta m
  have hu : 4≤u := h
  have h0 : 0<u := by linarith
  have hroot : 2≤Real.sqrt u := by nlinarith [Real.sq_sqrt h0.le,Real.sqrt_nonneg u]
  change 2*(Real.sqrt u)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_iff₀ (Real.sqrt_pos.mpr h0),one_mul]
  exact hroot

/-- The literal charged original Q input has this stronger quote at every
coupling and at the identical prescribed radii and physical path width. -/
theorem initial {B : MS.Local.Physical.Deck G} [Fintype V] (R : Run G) (hG : G.Simple)
    (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ)
    (profile : ∀ j,j≤(R.metals.p.profile j).order ∧ j≤(R.metals.p.profile j).power)
    (hm : ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
    (hperiod : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val) :
    let A' := ActualOriginalQInitialInput.schedule R hG u J A
    let F := ActualOriginalQInitialInput.input R hG u J A d Q o μ orders profile hm hperiod
    ∀ t : ℝ,F.packets.Paid (A'.inputNorm d.level) F.inputAddresses F.inputRegion
      (fun v=>F.inputRadii v / F.kernelCosts v) t (A'.inputWidth d.level) (A'.admittedCost d.level)
      F.coverOffset F.coverSlope := by
  intro A' F t
  exact unchanged F.packets F.input_paid (fun _=>rfl) t

/-- One scale threshold precedes all cutoffs, periods, tests, roots, and
the complete original unmasked coefficient bank. -/
theorem original {C : Family G} (hC : C.Makes) (Pτ : Poetry C.path.levels) (hG : G.Simple)
    (k r : ℕ) {η : ℝ} (hη : 0<η) (hη₁ : η<1) :
    ∀ᶠ m : ℕ in atTop, ∀ (N : ℕ) (_ : m≤N) (period : ℕ),
      let g := Pert.Asymptotics.regulatorRun C N period m
      ∀ (P : MarkedPackets D G (C.side m period) Γ) {q : BudgetPoint} {Y region w width budget a b},
      P.rankCap≤k → P.Paid q Y region w 1 width budget a b →
      ∀ (x : IndependentTests D) (v : V),
        SumBudget (charged (w:=w) (width:=width) P (scene C.path N period m) g x v r)
          (cap k*g^((r:ℝ)-η)*budget) := by
  filter_upwards [climate C.path.levels hG k hη hη₁,WilsonCurvatureEndpoints.original (D:=D) hC.wilson Pτ hG,small hC hG]
    with m hcl hμ hsmall
  intro N hm period
  dsimp only
  intro P q Y region w width budget a b hk H x v
  have hg₁ := hsmall N period hm
  let g := Pert.Asymptotics.regulatorRun C N period m
  have hg := IterationFour.Currency.g_pos hC N period m hm
  have hhat := (IterationFour.Currency.hat_g hC N period m hm).1
  have cost : 0≤cap k := by unfold cap;positivity
  apply graded P H _ x v r g η (cap k) hg hg₁ cost
  intro i T hi
  exact (hμ N hm period (P.rank i) T (testInclusion D x) ((H.coefficient i T hi).2 x)).trans
    (mul_le_mul_of_nonneg_left (hcl g hg hg₁ hhat (P.rank i) ((P.rank_bounded i T hi).trans hk))
      (H.coefficient i T hi).1)

end YM.Integration.ManuscriptQLocalKernelTariff
end

/-! The native healthy Wilson stencil at high total coupling degree. The
independent coefficients are bought before applying their Laurent powers.
The support-weighted derivative fee includes every chosen marked root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHealthyTariff

open Finset Filter Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token Push.AbsoluteSums
open ManuscriptQLocalPacketFootprint ManuscriptQLocalKernelTariff Next.Scheduling
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
  {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
  {q : BudgetPoint} {L : V → Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V → ℝ} {width budget : ℝ} {a b : ℕ}

theorem grade {g θ X : ℝ} {r cap t : ℕ} {e : ℤ}
    (hg : 0<g) (hg1 : g≤1) (hθ : 0≤θ) (hX : 1≤X)
    (hθX : θ≤X*g) (hgrade : (r:ℤ)≤e+t) (hcap : t≤cap) :
    ‖(g:ℂ)^e‖*θ^t ≤ g^r*X^cap := by
  have h := Real.rpow_le_rpow_of_exponent_ge hg hg1
    (show (r:ℝ)≤(e:ℝ)+(t:ℝ) by exact_mod_cast hgrade)
  rw [Real.rpow_add hg,Real.rpow_intCast,Real.rpow_natCast,Real.rpow_natCast] at h
  have ga : ‖(g:ℂ)^e‖=g^e := by
    rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hg.le]
  calc
    _ ≤ ‖(g:ℂ)^e‖*(X*g)^t := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ hθX _) (norm_nonneg _)
    _ = (g^e*g^t)*X^t := by rw [mul_pow,ga];ring
    _ ≤ _ := mul_le_mul h (pow_le_pow_right₀ hX hcap) (pow_nonneg (by linarith) _) (pow_nonneg hg.le _)

/-- Independent marked directions and all derivative lists from the native
supremum norm use the literal original high or low row. -/
theorem row (H : P.Paid q L region w 1 width budget a b)
    (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (v : V) (o : Site n) (ho : o∈L v)
    (i : ℕ) (hv : v∈(P.mode i).val)
    (T : Token G n (fun v=>(D v).Mood) (P.rank i)) (hT : P.packet i=some T) :
    p.supBounds o T.plot (fun U=>P.term (testInclusion D x) g U i)
      (‖(g:ℂ)^P.power i‖*touched p T) := by
  have h := ActualWilsonPacketGerms.address_germ H hT p x v hv o ho
  have hread : p.supBounds o T.plot (T.read (testInclusion D x)) (touched p T) := by
    simpa only [MarkedPackets.term,hT,Complex.ofReal_one,one_zpow,norm_one,one_mul] using h
  have actual : (fun U => P.term (testInclusion D x) g U i) =
      ((g:ℂ)^P.power i) • T.read (testInclusion D x) := by
    funext U
    simp [MarkedPackets.term,hT]
  rw [actual]
  exact Next.Foundations.bound_smul _ hread

def contribution (p : BudgetPoint) (v : V) (g : ℝ) (r i : ℕ) : ℝ :=
  if v∈(P.mode i).val ∧ (r:ℤ)≤P.power i+(P.rank i:ℤ) then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i)*p.mass T.plot (‖(g:ℂ)^P.power i‖*touched p T)
  else 0

/-- One complete address-rooted budget for the original high mixed grades.
The input price is the native unweighted path tariff on exactly that bank. -/
theorem total (H : P.Paid q L region w 1 width budget a b)
    (p : BudgetPoint) (hB : p.B=q.B)
    (hσ' : p.supportExponent≤2*q.supportExponent) (v : V) (r cap : ℕ) (hcap : P.rankCap≤cap)
    (g X : ℝ) (hg : 0<g) (hg1 : g≤1) (hX : 1≤X) (hθ : p.threshold≤X*g) :
    SumBudget (contribution (w:=w) P p v g r)
      ((ManuscriptQLocalPacketFootprint.fee G q.supportExponent p cap width*Real.exp ((p.supportExponent+1)*a)*g^r*X^cap)*budget) := by
  let C := ManuscriptQLocalPacketFootprint.fee G q.supportExponent p cap width
  have hs (t : ℕ) : 0≤2*Wages.startup G t p.power p.order :=
    mul_nonneg (by norm_num) (start_safe (t:=t) p G)
  have hslot : 0≤ManuscriptQLocalPacketFootprint.surcharge q.supportExponent :=
    zero_le_one.trans (le_max_left _ _)
  have hC : 0≤C := mul_nonneg (pow_nonneg hslot _) <|
    mul_nonneg (geometry_nonnegative _ _ _ (Nat.cast_nonneg _) H.width_pos)
      (sum_nonneg fun t _=>hs t)
  have hX₀ : 0≤X := by linarith
  let E := Real.exp ((p.supportExponent+1)*a)
  have hE : 0≤E := (Real.exp_pos _).le
  have hf : 0≤C*E*g^r*X^cap := by positivity
  apply budget_mono (budget_scale hf (quoted P H v))
  · intro i
    unfold contribution
    split
    · cases hi : P.packet i with
      | none => exact le_rfl
      | some T =>
        have start := start_safe (t:=P.rank i) p G
        have coin := (H.coefficient i T hi).1
        have temp := p.threshold_pos
        have span0 : 0≤touched p T := by
          unfold Token.touched units subtotal
          positivity
        exact mul_nonneg (Poly.worth H.positive _).le (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (norm_nonneg _) span0))
    · exact le_rfl
  · intro i
    by_cases h : v∈(P.mode i).val ∧ (r:ℤ)≤P.power i+(P.rank i:ℤ)
    · cases hi : P.packet i with
      | none => simp [contribution,ManuscriptQLocalKernelTariff.bare,h,hi]
      | some T =>
        have hrn := (P.rank_bounded i T hi).trans hcap
        have hv := ManuscriptQLocalPacketFootprint.token H hi p hB hσ' (P.rank i) cap le_rfl hcap
        have hgrade := grade hg hg1 p.threshold_pos.le hX hθ h.2 hrn
        have hcoin := (H.coefficient i T hi).1
        have toll := (Poly.worth H.positive (P.mode i)).le
        simp only [contribution,ManuscriptQLocalKernelTariff.bare,h,and_self,if_true,hi]
        calc
          _ = Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*p.mass T.plot (touched p T) := by
            unfold BudgetPoint.mass
            ring
          _ ≤ Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*
              (C*p.threshold^(P.rank i)*E*(T.coin*Real.exp (width*T.fall))) :=
            mul_le_mul_of_nonneg_left hv (mul_nonneg toll (norm_nonneg _))
          _ = (‖(g:ℂ)^P.power i‖*p.threshold^(P.rank i))*
              (C*E*Poly.toll w (P.mode i)*(T.coin*Real.exp (width*T.fall))) := by ring
          _ ≤ (g^r*X^cap)*(C*E*Poly.toll w (P.mode i)*(T.coin*Real.exp (width*T.fall))) :=
            mul_le_mul_of_nonneg_right hgrade (by positivity)
          _ = _ := by ring
    · have hn := (quoted P H v).1 i
      simpa only [contribution,if_neg h] using (mul_nonneg hf hn)

end YM.Integration.ManuscriptQLocalHealthyTariff
end

/-! The genuine paid kernel roster accepts a radius per mixed coupling
degree. The physical reader is held fixed while the original source charge
is multiplied by the radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedRadius
open Finset Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token Push.AbsoluteSums Next.Scheduling
open ManuscriptQLocalPacketFootprint ManuscriptQLocalHealthyTariff
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] {n : Side} {Γ : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
    {q : BudgetPoint} {L : V→Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {width budget : ℝ} {a b : ℕ}

def degree (i : ℕ) := (P.power i+(P.rank i:ℤ)).toNat

def amount (p : BudgetPoint) (v : V) (g ρ : ℝ) (i : ℕ) :=
  ρ^(degree P i) * contribution (w:=w) P p v g (degree P i) i

def price (G : Gauge) (q p : BudgetPoint) (cap off : ℕ) (width X budget : ℝ) :=
  fee G q.supportExponent p cap width*Real.exp ((p.supportExponent+1)*off)*X^cap*budget

private theorem degree_le {i : ℕ} {T : Token G n (fun v=>(D v).Mood) (P.rank i)}
    (hT : P.packet i=some T) : degree P i≤P.powerCap+P.rankCap := by
  have hp := P.power_bounded i T hT
  have hq := P.rank_bounded i T hT
  have h0 := P.nonnegative_grade i T hT
  unfold degree
  have hnat : P.power i≤((P.power i).natAbs:ℤ) := Int.le_natAbs
  omega

/-- The linear paid source mass holds simultaneously for the whole growing
radius, including the field-independent positive charges. -/
theorem boosted (H : P.Paid q L region w 1 width budget a b)
    (p : BudgetPoint) (hB : p.B=q.B) (hσ : p.supportExponent≤2*q.supportExponent)
    (v : V) (cap : ℕ) (hcap : P.rankCap≤cap) (g ρ X : ℝ)
    (hg : 0<g) (hg1 : g≤1) (hρ : 0≤ρ) (hr : ρ*g≤1)
    (hX : 1≤X) (hθ : p.threshold≤X*g) :
    SumBudget (amount (w:=w) P p v g ρ)
      ((P.powerCap+P.rankCap+1:ℕ)*price G q p cap a width X budget) := by
  let L₀ := fee G q.supportExponent p cap width*Real.exp ((p.supportExponent+1)*a)
  let value := fun e i => if degree P i=e then ρ^e*contribution (w:=w) P p v g e i else 0
  have h0 : 0≤price G q p cap a width X budget := by
    simpa [price] using budget_nonneg (total P H p hB hσ v 0 cap hcap g X hg hg1 hX hθ)
  have held (e : ℕ) : SumBudget (value e) (price G q p cap a width X budget) := by
    have hs := total P H p hB hσ v e cap hcap g X hg hg1 hX hθ
    have lifted := budget_scale (pow_nonneg hρ e) hs
    have small : (ρ*g)^e≤1 := pow_le_one₀ (mul_nonneg hρ hg.le) hr
    have bill : ρ^e*((L₀*g^e*X^cap)*budget)≤price G q p cap a width X budget := by
      calc
        _ = (ρ*g)^e * price G q p cap a width X budget := by unfold L₀ price;rw [mul_pow];ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right small h0).trans_eq (one_mul _)
    refine budget_mono (budget_loosen lifted bill) (fun i=>?_) (fun i=>?_)
    · unfold value
      split
      · exact mul_nonneg (pow_nonneg hρ _) (hs.1 i)
      · rfl
    · by_cases hh : degree P i=e
      · simp only [value,if_pos hh,le_refl]
      · simp only [value,if_neg hh]
        exact mul_nonneg (pow_nonneg hρ _) (hs.1 i)
  let cap₀ := P.powerCap+P.rankCap+1
  have all := budget_over (Finset.range cap₀) value (fun _=>price G q p cap a width X budget)
    (fun e _=>held e)
  have eqi : (fun i=>∑ e∈range cap₀,value e i)=amount (w:=w) P p v g ρ := by
    funext i
    cases hT : P.packet i with
    | none =>
      simp [value,amount,contribution,hT,apply_ite]
    | some T =>
      have hdeg : degree P i∈range cap₀ := mem_range.mpr (Nat.lt_succ_of_le (degree_le P hT))
      simp [value,amount,hdeg]
  rw [eqi] at all
  simpa only [sum_const,card_range,nsmul_eq_mul] using all

/-- A finite selection incurs at most one full rooted tariff per external
mark, independently of the size of the lattice. -/
theorem finite [Fintype V] (H : P.Paid q L region w 1 width budget a b)
    (p : BudgetPoint) (hB : p.B=q.B) (hσ : p.supportExponent≤2*q.supportExponent)
    (E : Finset ℕ) (T : (i : E)→Token G n (fun v=>(D v).Mood) (P.rank i))
    (chose : ∀i:E,P.packet i=some (T i))
    (cap : ℕ) (hcap : P.rankCap≤cap) (g ρ X : ℝ)
    (hg : 0<g) (hg1 : g≤1) (hρ : 0≤ρ) (hr : ρ*g≤1) (hX : 1≤X) (hθ : p.threshold≤X*g) :
    ∑ i : E,ρ^(degree P i)*Poly.toll w (P.mode i)*
      p.mass (T i).plot (‖(g:ℂ)^P.power i‖*touched p (T i)) ≤
      Fintype.card V*((P.powerCap+P.rankCap+1:ℕ)*price G q p cap a width X budget) := by
  have h := fun v=>boosted P H p hB hσ v cap hcap g ρ X hg hg1 hρ hr hX hθ
  calc
    _ ≤ ∑ i : E,∑ v : V,amount (w:=w) P p v g ρ i := by
      apply sum_le_sum
      intro i _
      obtain ⟨v,hv⟩ : (P.mode i).val.Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        exact fun h=>P.marked i (T i) (chose i) (Subtype.ext h)
      have deg : (degree P i:ℤ)≤P.power i+(P.rank i:ℤ) :=
        (Int.toNat_of_nonneg (P.nonnegative_grade i (T i) (chose i))).le
      apply le_trans _ (single_le_sum (fun j _=>(h j).1 i) (mem_univ v))
      simp only [amount,contribution,hv,deg,and_self,if_true,chose i]
      exact le_of_eq (by ring)
    _ = ∑ v : V,∑ i : E,amount (w:=w) P p v g ρ i := sum_comm
    _ ≤ ∑ _v:V,(P.powerCap+P.rankCap+1:ℕ)*price G q p cap a width X budget :=
      sum_le_sum fun v _=>by
        rw [Finset.sum_coe_sort]
        exact budget_sum (h v) E
    _ = _ := by simp [nsmul_eq_mul]
end YM.Integration.ManuscriptQLocalMarkedRadius
end

/-! Native real teams for the independent complex coordinates of the
submitted ordinary and compulsory activity bank. Gas indices and every
unselected compulsory partner retain their physical meaning. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedLeaves
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic LocalComparison PhysicalNext PhysicalNext.Repeat Lotus
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {R : Rep G n}

structure Slot (R : Rep G n) where
  turn : Wing
  field : Config G n → ℂ
  «scoped» : UsesFinal R.p.threshold (turn.support R) field
  allowed U : field U≠0 → turn.qualifies R U
  blank : turn.blank R
  charge : ℝ
  bounded U : ‖field U‖≤charge
  invariant : GaugeInvariant field
  measured : Measurable field

def draw (r : Slot R) (L : ℂ →L[ℝ] ℝ) : Leaf R where
  turn := r.turn
  ingredient U := L (r.field U)
  scopedR U V h h' := congrArg L (r.scoped U V h h')
  grant U h := r.allowed U (fun hz => h (by simp [hz]))
  blank := r.blank
  weight := ‖L‖*r.charge
  earn U := (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (r.bounded U) (norm_nonneg _))
  glows k U := congrArg L (r.invariant k U)
  borel := L.continuous.measurable.comp r.measured

/-- At a distinct genuine dormant ordinary address, a complex marked row
retains its original mask, not merely its value on the healthy set. -/
def ordinary (i : ℕ) (P : Support n) (F : Config G n → ℂ) (C : ℝ)
    (place : (R.activities.reg i).support=P) (spare : R.activities.E i = 0)
    (legal : R.p.Regular P F) (paid : 0≤C) (normOn : ∀ U, Healthy R.p.threshold P U → ‖F U‖≤C) : Slot R where
  turn := .logKey i
  field := masked R.p.threshold P F
  «scoped» := by
    change UsesFinal _ (R.activities.reg i).support _
    rw [place]
    intro U V agree hl
    have hg : Healthy R.p.threshold P U ↔ Healthy R.p.threshold P V := by
      unfold Healthy
      rw [Finset.disjoint_iff_inter_eq_empty,hl,Finset.disjoint_iff_inter_eq_empty]
    by_cases ha : Healthy R.p.threshold P U
    · rw [masked_eq _ _ _ _ ha,masked_eq _ _ _ _ (hg.mp ha),legal.sites U V agree]
    · rw [masked_ne _ _ _ _ ha,masked_ne _ _ _ _ (mt hg.mpr ha)]
  allowed U nz := by
    change Healthy R.p.threshold (R.activities.reg i).support U
    rw [place]
    exact Classical.byContradiction fun h => nz (masked_ne _ _ _ _ h)
  blank := spare
  charge := C
  bounded U := by
    by_cases h : Healthy R.p.threshold P U
    · simpa only [masked_eq _ _ _ _ h] using normOn U h
    · simpa only [masked_ne _ _ _ _ h,norm_zero] using paid
  invariant := Push.Local.Kernel.mask_gauge R.p.threshold P legal.symmetry
  measured := masked_measurable _ _ _ legal.borel

variable {α : Type} [Fintype α] [DecidableEq α] {Γ : Census α} {X : Type*}
  {o : α → Site n} {T : Taste X o R Γ} {w : α → ℝ} {κ a b : ℝ}

/-- Every compulsory slot in the applicant's full budget is an actual native
gas-key insertion at its own old index on every field. -/
def forced (B : FullBudget R.p T w κ a b) (x : X) (i j : ℕ) : Slot R where
  turn := .gasKey i
  field := T.menu.force x i j
  «scoped» := (B.active x).articles.inspects i j
  allowed U := (B.active x).articles.keeps i j U
  blank := trivial
  charge := B.black (i,j)
  bounded := B.forced x i j
  invariant := (B.active x).articles.invi i j
  measured := (B.active x).articles.meas i j

/-- Repeated source footprints are allowed. Only their protected original
slot labels must be distinct inside a simultaneous product. -/
def regular (B : FullBudget R.p T w κ a b) (x : X) (row key : ℕ)
    (place : (R.activities.reg key).support = T.menu.branch row) (spare : R.activities.E key=0) : Slot R :=
  ordinary key (T.menu.branch row) (T.menu.regular x row) (B.white row) place spare
    (B.regular_law x row) (B.white_nonnegative row) (by
      obtain ⟨v,hv⟩ := (B.active x).articles.proper row
      exact grain_value ((B.regular row).controls x v hv))

variable {ι : Type} [Fintype ι] [DecidableEq ι] (rows : ι → Slot R)
  (distinct : Injective (fun i => (rows i).turn)) (L : ι → ℂ →L[ℝ] ℝ)

def team : Lotus.Team R where
  own := Finset.univ.image (fun i => draw (rows i) (L i))
  alone := by
    intro a ha b hb he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact congrArg (fun i => draw (rows i) (L i)) (distinct he)

omit [DecidableEq ι] in
theorem ingredients (U : Config G n) :
    (team rows distinct L).ingredients U = ∏ i, L i ((rows i).field U) := by
  unfold Lotus.Team.ingredients
  change (∏ y∈Finset.univ.image (fun i => draw (rows i) (L i)),y.ingredient U) = _
  rw [Finset.prod_image]
  · rfl
  · intro i _ j _ h
    exact distinct (congrArg Leaf.turn h)

def demanded : Finset ℕ :=
  (Finset.univ.image (fun i => match (rows i).turn with
    | .logKey _ => (Sum.inl () : Unit ⊕ ℕ) | .gasKey j => Sum.inr j)).toRight

omit [DecidableEq ι] in
theorem due : (team rows distinct L).gasDue = demanded rows := by
  ext i
  rw [Lotus.Team.asked]
  simp only [team,Finset.mem_image,Finset.mem_univ,true_and,exists_exists_eq_and,draw,demanded,Finset.mem_toRight]
  constructor
  · rintro ⟨j,h⟩
    exact ⟨j,by rw [h]⟩
  · rintro ⟨j,h⟩
    exact ⟨j,by cases e:(rows j).turn with
      | logKey k => simp [e] at h
      | gasKey k => simpa [e] using h⟩

def remainder (R : Rep G n) (s : Finset ℕ) (U : Config G n) :=
  ∑' k : Finset ℕ, if R.activities.admissible R.p U k ∧ s ⊆ k then
    ∏ i ∈ k\s, R.activities.K i U else 0

omit [DecidableEq ι] in
theorem cofactor (U : Config G n) :
    (team rows distinct L).cicada U =
      Real.exp (R.exponent U)*((∏ i, L i ((rows i).field U))*remainder R (demanded rows) U) := by
  unfold Lotus.Team.cicada remainder
  apply congrArg (Real.exp (R.exponent U)*·)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold Lotus.Team.bun Lotus.Team.bill
  rw [due rows distinct L,ingredients rows distinct L U]
  by_cases h : R.activities.admissible R.p U k <;> by_cases hs : demanded rows ⊆ k <;> simp [h,hs]

end YM.Integration.ManuscriptQLocalMarkedLeaves
end

/-! A finite family of original complex inputs in the manuscript's native
retained-source offer. Its physical radii, punctures, signed coefficients and
prices are attached to all modes of the same source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedOffers
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open PhysicalNext.Repeat Lotus MergeProof MergeProof.Menu MergeProof.Accent Push.Local Extra.Trajectories
open ManuscriptQLocalMarkedLeaves
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {R : Rep G n} {ι V : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq V] {Γ : Census V} (rows : ι → Slot R) (mode : ι → Γ.Mode) (w : V → ℝ)

structure Ticket where
  terms : ι × Bool → Menu.Hat Γ R
  place i s : Menu.WKey (terms (i,s))=(rows i).turn ∧ (terms (i,s)).s=mode i
  fares i : ∑ s,Menu.fare (terms (i,s)) w=2*(Poly.toll w (mode i)*(rows i).charge)
  entry i U : ∑ s,Menu.amount (terms (i,s)) U=Poly.send (mode i) ((rows i).field U)

def polar (s:Bool) : ℂ →L[ℝ] ℝ :=
  if s then Complex.reCLM else Complex.imCLM

theorem polar_norm (s:Bool) : ‖polar s‖=1 := by
  cases s
  · have upper:‖Complex.imCLM‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun z=>by simpa only [Complex.imCLM_apply,Real.norm_eq_abs,one_mul] using Complex.abs_im_le_norm z)
    refine le_antisymm upper ?_
    simp [polar]
  · exact Complex.reCLM_norm

def components (hot:∀i,(mode i).val.Nonempty) (s:ι×Bool):Menu.Hat Γ R :=
  ⟨draw (rows s.1) (polar s.2),mode s.1,hot s.1,if s.2 then 1 else Complex.I⟩

def ticket (hot : ∀ i,(mode i).val.Nonempty) : Ticket rows mode w where
  terms:=components rows mode hot
  place _ _:=⟨rfl,rfl⟩
  fares i:=by
    rw [Fintype.sum_bool]
    simp only [Menu.fare,Menu.sumFee,components,draw,polar_norm,Bool.false_eq_true,if_false,if_true,
      norm_one,Complex.norm_I,one_mul]
    ring
  entry i U:=by
    rw [Fintype.sum_bool,Menu.varnish,Menu.varnish]
    change Poly.send (mode i) ((Complex.re ((rows i).field U):ℂ)*1)+
      Poly.send (mode i) ((Complex.im ((rows i).field U):ℂ)*Complex.I)=_
    rw [← Extra.Trajectories.send_add,mul_one]
    exact congrArg (Poly.send (mode i)) (Complex.re_add_im _)

namespace Ticket
variable {rows mode w} (T : Ticket rows mode w)

omit [DecidableEq ι] in
theorem grouped (k : Wing) (U : Config G n) :
    Menu.rush T.terms k U=∑ i, if (rows i).turn=k then Poly.send (mode i) ((rows i).field U) else 0 := by
  unfold Menu.rush
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [(T.place i _).1]
  by_cases h : (rows i).turn=k
  · simp only [if_pos h,T.entry]
  · simp [h]

variable (o : V → Site n) {rate : ℝ}

omit [DecidableEq ι] in
theorem price (hw : ∀ v,0<w v)
    (sites : ∀ i,(mode i).val.image o ⊆ (rows i).turn.support R)
    (paid : ∑ i,Poly.toll w (mode i)*R.p.mass ((rows i).turn.support R) (rows i).charge≤rate) :
    Menu.Offer o T.terms w R.p.B R.p.supportExponent (2*rate) := by
  have crest (i : ι) (s : Bool) : (T.terms (i,s)).M.crest=(rows i).turn.support R :=
    congrArg (fun t : Wing=>t.support R) (T.place i s).1
  refine ⟨fun ⟨i,s⟩ => (T.place i s).2.symm ▸ (crest i s).symm ▸ sites i,fun z => ?_⟩
  refine ⟨fun t=>by dsimp only; split; exact mul_nonneg (Menu.Crew w hw) (Real.exp_pos _).le; rfl,Summable.of_finite,?_⟩
  rw [tsum_fintype,Fintype.sum_prod_type]
  apply le_trans _ (mul_le_mul_of_nonneg_left paid zero_le_two)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp_rw [crest]
  by_cases hz : z∈(rows i).turn.support R
  · simp only [if_pos hz,←Finset.sum_mul,T.fares,BudgetPoint.mass]
    exact le_of_eq (by ring)
  · simp only [if_neg hz,Finset.sum_const_zero]
    exact mul_nonneg zero_le_two (mul_nonneg (Poly.worth hw _).le
      (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans ((rows i).bounded 1))))

variable [Fintype V] {σ α Λ e b : ℝ} {c : Side} (S : StepData c n)

omit [Fintype V] [DecidableEq ι] in
/-- The native palette contains every admissible original spectator set,
including all unaffected scalar K, before integrating over the fine field. -/
theorem expense (hw : ∀ v,0<w v) (hR : R.Lawful σ α Λ e b) (U : Config G n) :
    Menu.Expense T.terms w S U=(Real.exp (R.exponent U):ℂ) •
      ((∏ j∈Menu.logDeck T.terms,(1+∑ i, if (rows i).turn=.logKey j then
          Poly.send (mode i) ((rows i).field U) else 0)) *
       ∑' a : Finset ℕ, if R.activities.admissible R.p U a then
         ∏ j∈a,(Poly.bead Γ (R.activities.K j U : ℂ) +
          ∑ i, if (rows i).turn=.gasKey j then Poly.send (mode i) ((rows i).field U) else 0) else 0) := by
  rw [Menu.Expense,Menu.passIn T.terms S hR hw U,←Menu.win T.terms hR U]
  rw [rock_out R.activities R.p U _ hw (Menu.fence T.terms hR hw U).1]
  simp only [Menu.jets,Menu.Kunt,T.grouped]

end Ticket
end YM.Integration.ManuscriptQLocalMarkedOffers
end

/-! Realized source radii for the genuinely healthy primitive Wilson packet
rows. The finite color phase pairs share the same original representation,
dormant addresses, physical aperture and independent unit tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHealthyOffer
open Function Finset Lattice Wilson RG Marker LocalComparison
open Progress.DirectedRecipe Comparison.Density.RenderM Comparison.Density.RenderM.Token
open PhysicalNext.Repeat Lotus MergeProof MergeProof.Menu Push.Local Push.AbsoluteSums
open ManuscriptQLocalMarkedLeaves ManuscriptQLocalMarkedOffers ManuscriptQLocalMarkedRadius
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {D : V → ComparisonDensity.Address.Orbit} {P : MarkedPackets D G n Γ}
  {q : BudgetPoint} {L : V→Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V→ℝ} {width budget : ℝ} {a b : ℕ}
  (H : P.Paid q L region w 1 width budget a b)
  (o : V→Site n) (ho : ∀v,o v∈L v)
  {E : Finset ℕ} (T : (i : E)→Token G n (fun v=>(D v).Mood) (P.rank i))
  (chose : ∀i:E,P.packet i=some (T i))

omit [Fintype V] in
include T chose in
private theorem hot (i : E) : (P.mode i).val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (fun h=>P.marked i (T i) (chose i) (Subtype.ext h))

def address (i : E) : RegularAddress n :=
  let v := (hot T chose i).choose
  ⟨o v,(T i).plot, H.addresses i (T i) (chose i) v (hot T chose i).choose_spec (ho v)⟩

/-- Regular addresses are secured through an authentic dormant-slot
presentation. The slot supports remain the literal full packet plots. -/
def block (Y : Rep G n) (slot : E→ℕ) (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (g : ℝ) (x : IndependentTests D) (i : E) : Slot Y := by
  let v := (hot T chose i).choose
  have hr := ManuscriptQLocalHealthyTariff.row P H p g x v (o v) (ho v) i
    (hot T chose i).choose_spec (T i) (chose i)
  have hf : Y.p.Regular (T i).plot (fun U=>P.term (testInclusion D x) g U i) := by
    have hz : (fun U=>P.term (testInclusion D x) g U i) =
        ((g:ℂ)^P.power i) • (T i).read (testInclusion D x) := by
      funext U
      simp [MarkedPackets.term,chose]
    rw [hz]
    exact Next.Foundations.regular_smul _ (ActualWilsonPacketGerms.regular_at H (chose i) Y.p (testInclusion D x))
  refine ManuscriptQLocalMarkedLeaves.ordinary (slot i) (T i).plot
    (fun U=>P.term (testInclusion D x) g U i)
    (‖(g:ℂ)^P.power i‖*touched p (T i)) (placed i) (spare i) hf hr.1 ?_
  intro U hU
  rw [ht] at hU
  exact hr.2 U hU [] (Nat.zero_le _) (by simp)

/-- Explicit signed physical leaves, with the two fixed original real
projections at each incoming packet. -/
def menu (Y : Rep G n) (slot : E→ℕ) (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (g : ℝ) (x : IndependentTests D) : E×Bool→Menu.Hat Γ Y :=
  (ticket (block H o ho T chose Y slot placed spare p ht g x)
     (fun i:E=>P.mode i) w (hot T chose)).terms

omit [Fintype V] in
theorem menu_weight (Y : Rep G n) (slot : E→ℕ) (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (g : ℝ) (x : IndependentTests D) (i:E) (s:Bool) :
    ((menu H o ho T chose Y slot placed spare p ht g x (i,s)).M).weight =
      ‖ManuscriptQLocalMarkedOffers.polar s‖*(‖(g:ℂ)^P.power i‖*touched p (T i)) := rfl

omit [Fintype V] in
theorem menu_ingredient (Y : Rep G n) (slot : E→ℕ) (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (g : ℝ) (x : IndependentTests D) (i:E) (s:Bool) (U:Config G n) :
    ((menu H o ho T chose Y slot placed spare p ht g x (i,s)).M).ingredient U =
      ManuscriptQLocalMarkedOffers.polar s
        (masked Y.p.threshold (T i).plot (fun V=>P.term (testInclusion D x) g V i) U) := rfl

/-- The same literal native Hat with its original scalar charge at the
announced radius. This is the gradedHat used by the retained orbit. -/
def raised {Y : Rep G n} (M : Menu.Hat Γ Y) (ρ : ℝ) (d : ℕ) : Menu.Hat Γ Y :=
  {M with charge := M.charge*(ρ:ℂ)^d}

omit [Fintype V] in
theorem fare {Y : Rep G n} (M : Menu.Hat Γ Y) (ρ : ℝ) (hρ : 0≤ρ) (d : ℕ) :
    Menu.fare (raised M ρ d) w=ρ^d*Menu.fare M w := by
  simp only [raised,Menu.fare,Menu.sumFee,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hρ]
  ring

/-- The original unboosted rows agree pointwise with the physically masked
Wilson test. The separate booked offer buys their declared scalar source
radii, on every mode and every original spatial root, before the integration. -/
theorem issued (Y : Rep G n) (slot : E→ℕ)
    (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (hB : p.B=q.B) (hσ : p.supportExponent≤2*q.supportExponent)
    (cap : ℕ) (hcap : P.rankCap≤cap) (g ρ X : ℝ) (x : IndependentTests D)
    (hg : 0<g) (hg₁ : g≤1) (hρ : 0≤ρ) (hr : ρ*g≤1) (hX : 1≤X) (hθ : p.threshold≤X*g) :
    let M:=menu H o ho T chose Y slot placed spare p ht g x;
      (∀ (i:E) (s:Bool),(M (i,s)).s=P.mode i ∧ Menu.WKey (M (i,s))=.logKey (slot i)) ∧
      (∀ (i:E) U,∑ s,Menu.amount (M (i,s)) U =
        Poly.send (P.mode i) (masked p.threshold (T i).plot (fun U=>P.term (testInclusion D x) g U i) U)) ∧
      Menu.Offer o (fun t=>raised (M t) ρ (degree P t.1)) w p.B p.supportExponent
        (2*(Fintype.card V*((P.powerCap+P.rankCap+1:ℕ)*price G q p cap a width X budget))) := by
  let R := block H o ho T chose Y slot placed spare p ht g x
  let M := ticket R (fun i : E=>P.mode i) w (hot T chose)
  have crest (i : E) (s : Bool) : (M.terms (i,s)).M.crest=(T i).plot :=
    (congrArg (fun t : Wing=>t.support Y) (M.place i s).1).trans (placed i)
  refine ⟨fun i s=>⟨(M.place i s).2,(M.place i s).1⟩,?_,?_⟩
  · intro i U
    change (∑ s,Menu.amount (M.terms (i,s)) U)=_
    rw [M.entry]
    change Poly.send (P.mode i) (masked Y.p.threshold (T i).plot
      (fun V:Config G n=>P.term (testInclusion D x) g V i) U) = _
    rw [ht]
  · refine ⟨?_,?_⟩
    · intro ⟨i,s⟩
      change (M.terms (i,s)).s.val.image o ⊆ (M.terms (i,s)).M.crest
      rw [(M.place i s).2,crest]
      exact Finset.image_subset_iff.mpr fun v hv => H.addresses i (T i) (chose i) v hv (ho v)
    intro z
    refine ⟨fun t=>by dsimp only; split; exact mul_nonneg (Menu.Crew w H.positive) (Real.exp_pos _).le; rfl,
      Summable.of_finite,?_⟩
    rw [tsum_fintype,Fintype.sum_prod_type]
    have bound := ManuscriptQLocalMarkedRadius.finite P H p hB hσ E T chose cap hcap g ρ X hg hg₁ hρ hr hX hθ
    apply le_trans _ (mul_le_mul_of_nonneg_left bound zero_le_two)
    rw [Finset.mul_sum]
    refine sum_le_sum fun i _=>?_
    change (∑ s,if z∈(M.terms (i,s)).M.crest then
      Menu.fare (raised (M.terms (i,s)) ρ _) w*Real.exp (p.supportExponent*coverNumber p.B ((M.terms (i,s)).M.crest))
      else 0) ≤ _
    simp_rw [crest]
    by_cases hz : z∈(T i).plot
    · simp only [if_pos hz,fare (w:=w) _ _ hρ,←Finset.sum_mul,←Finset.mul_sum,M.fares,
        BudgetPoint.mass]
      apply le_of_eq
      change ρ^degree P i*(2*(Poly.toll w (P.mode i)*(‖(g:ℂ)^P.power i‖*touched p (T i))))*_=_
      ring
    · simp only [if_neg hz,Finset.sum_const_zero]
      have hc := (ManuscriptQLocalHealthyTariff.row P H p g x (hot T chose i).choose
        (o (hot T chose i).choose) (ho _) i (hot T chose i).choose_spec (T i) (chose i)).1
      exact mul_nonneg zero_le_two
        (mul_nonneg (mul_nonneg (pow_nonneg hρ _) (Poly.worth H.positive _).le) (mul_nonneg (Real.exp_pos _).le hc))
include H ho chose in
theorem offer (Y : Rep G n) (slot : E→ℕ)
    (placed : ∀i,(Y.activities.reg (slot i)).support=(T i).plot)
    (spare : ∀i,Y.activities.E (slot i)=0) (p : BudgetPoint) (ht : Y.p.threshold=p.threshold)
    (hB : p.B=q.B) (hσ : p.supportExponent≤2*q.supportExponent)
    (cap : ℕ) (hcap : P.rankCap≤cap) (g ρ X : ℝ) (x : IndependentTests D)
    (hg : 0<g) (hg₁ : g≤1) (hρ : 0≤ρ) (hr : ρ*g≤1) (hX : 1≤X) (hθ : p.threshold≤X*g) :
    ∃ M : E×Bool→Menu.Hat Γ Y,
      (∀ (i:E) (s:Bool),(M (i,s)).s=P.mode i ∧ Menu.WKey (M (i,s))=.logKey (slot i)) ∧
      (∀ (i:E) U,∑ s,Menu.amount (M (i,s)) U =
        Poly.send (P.mode i) (masked p.threshold (T i).plot (fun U=>P.term (testInclusion D x) g U i) U)) ∧
      Menu.Offer o (fun t=>raised (M t) ρ (degree P t.1)) w p.B p.supportExponent
        (2*(Fintype.card V*((P.powerCap+P.rankCap+1:ℕ)*price G q p cap a width X budget))) := by
  exact ⟨menu H o ho T chose Y slot placed spare p ht g x,
    issued H o ho T chose Y slot placed spare p ht hB hσ cap hcap g ρ X x hg hg₁ hρ hr hX hθ⟩

end YM.Integration.ManuscriptQLocalHealthyOffer
end
