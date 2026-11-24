import YM.Integration.WilsonThermometerProgramFinitePages
import YM.FVAAlt2.Boot.Labels

/-! The numerical birth's ordinary faces on an arithmetic copy are actual finite
sums of the original position submissions at the independently lifted child sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerProgramSubmittedWords
open Finset Function Lattice Wilson RG QuadraticLocal QuadraticLocal.Sunrise Marker Comparison.RG02
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 FVA1Physical.TwoReset
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick WilsonCoeffUV AllOrder AllOrder.Floe
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [Fintype V] [LinearOrder V]
    (d : V → ℕ) {n f : Side} (o : V → Site n) (g τ : ℝ)
    (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ)
    (h : n.val ∣ f.val) (x : T) (u : ℝ) (U : Config G f)
local notation "J" => Stock.census V

def dose (j : V) : Option (R.family.labels.level (d j)).Index → ℂ
  | none => t j x * v j 0
  | some a => (((g/τ)^(ActualRunGradedKernels.rank R (d j) a) : ℝ):ℂ) *
      (t j x * ((R.family.labels.level (d j)).core (v j)) a)

def row (j : V) (z : Site f) : Option (R.family.labels.level (d j)).Index → ℂ
  | none => 1
  | some a => ((u : ℂ)^(ActualRunGradedKernels.rank R (d j) a))⁻¹ *
      (R.family.localSection (d j)).places (Pi.single a 1) z U

omit [Fintype V] [LinearOrder V] in
private theorem billed (j : V) (z : Site f) :
    WilsonThermometerProgramFinitePages.atSite R d g τ v t x u U j z =
      ∑ b, dose R d g τ v t x j b * row R d u U j z b := by
  rw [Fintype.sum_option]
  change t j x * v j 0 + _ = t j x * v j 0 * 1 + _
  rw [mul_one]
  apply congrArg (fun w : ℂ => t j x * v j 0 + w)
  apply Finset.sum_congr rfl
  intro a _
  simp only [dose,row,WilsonThermometerProgramBasis.weight,div_eq_mul_inv, mul_pow,
    Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_inv,inv_pow]
  ring

variable (sites : Finset V)
abbrev Choice (n f : Side) (S : Finset V) :=
  (j : ↥S) → Fin (Pages n f) × Option (R.family.labels.level (d j.val)).Index
def live (q : Choice R d n f sites) : Finset ↥sites :=
  univ.filter fun j => (q j).2.isSome
def axis (q : Choice R d n f sites) (j : ↥sites) :=
  (q j).2.getD 0
def coords (q : Choice R d n f sites) (j : ↥sites) : Cover :=
  lift (page h (o j.val) (q j).1).val
local notation "inc" => (fun j : ↥sites => d j.val)
local notation "W" q => Boot.scout R (live R d sites q) (inc) (axis R d sites q) (coords R d o h sites q)
local notation "ell" q => depthF (live R d sites q) (inc) (axis R d sites q)

omit [Fintype V] in
private theorem whole (q : Choice R d n f sites) :
    (∏ j : ↥sites, row R d u U j.val (page h (o j.val) (q j).1).val (q j).2) =
    ((u : ℂ) ^ (ell q))⁻¹ * (((W q).Vt f U : ℝ):ℂ) := by
  let H := live R d sites q
  have subset := Finset.prod_subset (s₁:=H) (s₂:=univ) (f:=fun j : ↥sites =>
    row R d u U j.val (page h (o j.val) (q j).1).val (q j).2) (subset_univ _)
  rw [← subset (fun j _ hj => by
    cases proof : (q j).2 with
    | none => rfl
    | some a => exact (hj (by simp [H,live,proof])).elim)]
  have chosen (j : ↥sites) (hj : j ∈ H) : (q j).2 = some (axis R d sites q j) := by
    cases proof : (q j).2 with
    | none => simp [H,live,proof] at hj
    | some a => simp [axis,proof]
  have sheet := congrFun (Boot.combined R H (inc) (axis R d sites q) (coords R d o h sites q) f) U
  simp only [Function.comp_apply, coords,wrap_lift] at sheet
  change (Kick.topMark (Lodge.basisR R) H (inc) (axis R d sites q) f (coords R d o h sites q) U : ℂ) = _ at sheet
  change _ = ((u : ℂ) ^ (ell q))⁻¹ * (Kick.topMark _ H _ _ f _ U : ℂ)
  rw [sheet]
  calc
    _ = ∏ j ∈ H, ((u:ℂ)^ActualRunGradedKernels.rank R (d j.val) (axis R d sites q j))⁻¹ *
        (R.family.localSection (d j.val)).places (Pi.single (axis R d sites q j) 1)
          (page h (o j.val) (q j).1).val U := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [chosen j hj]
      rfl
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      congr 2
      · exact Finset.prod_pow_eq_pow_sum _ _ _
      · exact (Finset.prod_apply U H _).symm

variable (L : Layout G) (pay : Finset Age)
local notation "inputs" => WilsonThermometerNumericalBank.bank R d o g τ v t h x L pay

/-- The signed coefficients are fixed at the elected fit. Every inverse power of
the formal argument belongs to its submitted position word. -/
theorem submitted (s : (Stock.census V).Mode) (hu : u ≠ 0) :
    (Poly.pass (Integral.markedLog u U (inputs))).part s =
      ∑ q : Choice R d n f s.val,
        (∏ j : ↥s.val, dose R d g τ v t x j.val (q j).2) *
          (((u:ℂ) ^ (depthF (live R d s.val q) (fun j : ↥s.val => d j.val) (axis R d s.val q)))⁻¹ * (((Boot.scout R (live R d s.val q) (fun j : ↥s.val => d j.val) (axis R d s.val q) (coords R d o h s.val q)).Vt f U : ℝ):ℂ)) := by
  rw [WilsonThermometerProgramFinitePages.all_faces R d o g τ v t h x L pay u U hu s]
  rw [← Finset.prod_coe_sort s.val (fun j => ∑ p : Fin (Pages n f),
    WilsonThermometerProgramFinitePages.atSite R d g τ v t x u U j (page h (o j) p).val)]
  calc
    _ = ∏ j : ↥s.val, ∑ c : Fin (Pages n f) × Option (R.family.labels.level (d j.val)).Index,
        dose R d g τ v t x j.val c.2 * row R d u U j.val (page h (o j.val) c.1).val c.2 := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun p _ => billed R d g τ v t x u U j.val (page h (o j.val) p).val
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.prod_mul_distrib,whole]

end YM.Integration.WilsonThermometerProgramSubmittedWords
