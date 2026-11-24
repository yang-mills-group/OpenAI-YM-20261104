import YM.Integration.WilsonOriginalStarSceneRent
import YM.Next.WARD_BIN.Coin

/-! Charge a deposited primary row at the grade of its original source. The
rank of the transported word may be larger than this grade; its Laurent
pole is the number of fields in the original graded basis vector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarGradedScene
open Function Finset Lattice Wilson RG Source Labels Marker LocalComparison QuadraticLocal
open Earn Sunrise PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [Fintype V] [DecidableEq V] (d : V → ℕ)

omit [Fintype V] [DecidableEq V] in
theorem pole_grade (i : Entry R d) : pole R d i ≤ d (root R d i) := by
  rcases i with j | ⟨j,w,a⟩
  · exact Nat.zero_le _
  · exact WardBin.basis_degree w

def credit (positive : ∀j,0<d j) (i : Entry R d) : Loan where
  e := rank R d i - pole R d i
  r := rank R d i
  toll := d (root R d i)
  higher := positive _
  crest := by have bound:=pole_grade R d i; have current:=low R d i; omega

variable {n : Side} (o : V → Site n) (σ g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t : V → T → ℂ)

def words (positive : ∀j,0<d j) (i:Entry R d) : Row (Passport.point o) (Stock.census V) G T :=
  {rows R d o σ g τ v t i with lamp:=credit R d positive i}

variable (positive : ∀j,0<d j)
local notation "M" => words R d o σ g τ v t positive
local notation "U" => rows R d o σ g τ v t
local notation "J" => Stock.census V

theorem rendered_same (B : BudgetPoint) (h:ℝ) : rendered M B h=rendered U B h := rfl

theorem issued (order : ℕ) (fit : maximum R d ≤ order) : Issues M σ order d := by
  refine ⟨fun i=>unitPrice _ _,fun i=>⟨?_,?_⟩⟩
  · exact ((WilsonOriginalStarSceneRows.original R d o σ g τ v t order fit).usable i).1
  · change d (root R d i)=∑j∈({root R d i}:Finset V),d j
    simp

theorem fleet (w:V→ℝ) (hw:∀j,0<w j) (ht:∀i x,‖t i x‖≤1)
    (order count shelf:ℕ) (fit:maximum R d≤order) (slots:Fintype.card V≤count) (space:∑i,d i ≤ shelf) :
    Scene.Armada M w d σ (bill R d σ g τ v w) order count shelf :=
  ⟨⟨fun s=>s.val.card_le_univ.trans slots,fun s=>(sum_le_sum_of_subset (subset_univ s.val)).trans space⟩,
    hw,offers R d o σ g τ v t w hw,issued R d o σ g τ v t positive order fit,honored R d o σ g τ v t ht⟩

theorem appointed {K Ω : ℝ} (non:0≤K) (cap:∀j,(R.family.labels.level (d j)).coeffSize (v j)≤K)
    (ready:0≤g) (warm:0<τ) (band:g≤2*τ) (one:1≤Ω) (ht:∀i x,‖t i x‖≤1)
    (order count shelf stage vac coarse:ℕ) (slots:Fintype.card V≤count) (space:∑i,d i ≤ shelf)
    (fit:maximum R d≤order) (room:order+1 ≤ stage) (future:order≤coarse) (stamp:∀i,d i≤coarse)
    (cover:order+shelf≤AllOrder.Burn.horizon vac+2) :
    let E:=max 1 ((1+K)*wallet R d σ)
    let w:=fun _ : V=>(E*Ω)⁻¹
    Scene.Armada M w d σ Ω⁻¹ order count shelf ∧ Mentor.Cruise.Voter M σ order count stage vac coarse ∧
      ∀ s:(J).Mode, Poly.toll w s*(E*Ω)^s.val.card=1 := by
  let E:=max 1 ((1+K)*wallet R d σ)
  have hE:1≤E:=le_max_left ..
  have hΩ:1≤E*Ω:=one_le_mul_of_one_le_of_one_le hE one
  let X:=fleet R d o σ g τ v t positive (fun _=>1) (fun _=>zero_lt_one) ht order count shelf fit slots space
  have base:bill R d σ g τ v (fun _=>1)≤E:=(allowance R d σ g τ v non cap ready warm band).trans (le_max_right ..)
  have fee:(E*Ω)⁻¹*bill R d σ g τ v (fun _=>1)≤Ω⁻¹:=by
    calc
      _ ≤ (E*Ω)⁻¹*E := mul_le_mul_of_nonneg_left base (inv_nonneg.mpr (zero_le_one.trans hΩ))
      _ = _ := by field_simp
  refine ⟨?_,⟨fun i=>?_,X.quota,room,fun C=>?_⟩,fun s=>?_⟩
  · have rad:Stoop.radius (fun _:V=>1) (E*Ω)=fun _=>(E*Ω)⁻¹:=by funext i; exact one_div _
    rw [←rad]
    exact (X.stored hΩ).higher fee
  · exact ⟨X.honor _,X.purchases.spend _,((X.purchases.usable i).1).trans future,stamp _⟩
  · rw [Press.tall M C d X.purchases.usable]
    exact (Nat.add_le_add_left (X.crew _) _).trans cover
  · change (∏ _∈s.val,(E*Ω)⁻¹)*(E*Ω)^s.val.card=1
    rw [prod_const,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ (zero_lt_one.trans_le hΩ).ne')]

end YM.Integration.WilsonOriginalStarGradedScene
