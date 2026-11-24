import YM.Integration.WilsonReceivedSourceRowJet
import YM.Integration.WilsonFirstReceivedIssuedIncome
import YM.Integration.WilsonOriginalMarkedEvaluation

/-! Rooted, signed comparison of the physical group-field value of the complete
issued roster with the independently filed finite list of its coupling grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceRoster
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Floe.Step
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X ι : Type} [DecidableEq V] {G : Gauge} {n : Side} {P : Passport n V} {Γ : Census V}

def error (T : Row P Γ G X) (x : X) (g : ℝ) (A : Link G n) (p : ℕ) : ℂ :=
  T.nominal g x (Integral.sample g (arm G n 1 A)) -
    ∑ j ∈ range (p+1), (g:ℂ)^j * (T.paint x * (T.markReceipt j A : ℂ))

def tariff (G : Gauge) (σ cap g : ℝ) (p shelf : ℕ) : ℝ :=
  (max 1 (2*(G.colorScale*cap)/σ))^(p+shelf+2) * g^(p+1)

variable (M : ι → Row P Γ G X) (w : V → ℝ) (grades : V → ℕ) {σ c : ℝ} {p count shelf : ℕ}
  (estate : Scene.Armada M w grades σ c p count shelf) (hs : 0 < σ)
  (x : X) (A : Link G n) {cap : ℝ} (hc : 0 ≤ cap) (axis : ∀ e, ‖collect G (arm G n 1 A) e‖ ≤ cap)
  {g : ℝ} (gp : 0 < g)
include estate hs hc axis gp

private theorem entry (i : ι) :
    ‖error (M i) x g A p‖ ≤ (M i).salary * tariff G σ cap g p shelf := by
  have rank := Scene.Armada.degreeR grades estate.toMinistry (M i) (estate.purchases.usable i)
  have one := WilsonReceivedSourceRowJet.priced (M i) (estate.honor i) hs (estate.purchases.spend i)
     x A hc axis p rank.1 gp
  let a := 2*(G.colorScale*cap)/σ
  have a0 : 0 ≤ a := div_nonneg (mul_nonneg (by norm_num) (mul_nonneg G.colorScale_pos.le hc)) hs.le
  have hi := (M i).lamp.crest
  have hn : p-(M i).lamp.e+(M i).lamp.r+1 ≤ p+shelf+2 := by omega
  have fee : a^(p-(M i).lamp.e+(M i).lamp.r+1) ≤ (max 1 a)^(p+shelf+2) :=
    (pow_le_pow_left₀ a0 (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hn)
  rw [tariff,← mul_assoc]
  exact one.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left fee (M i).sound.le) (pow_nonneg gp.le _))

/-- Every error retains the enrolled center and its full original exponential length tariff. -/
theorem rooted (o : Site n) :
    SumBudget (fun i => if (M i).center=o then Poly.toll w (M i).mode * ‖error (M i) x g A p‖ *
      Real.exp (σ*(M i).length) else 0) (tariff G σ cap g p shelf*c) := by
  have non : 0 ≤ tariff G σ cap g p shelf := by unfold tariff; positivity
  refine Push.PriceCompiler.sumBudget_mono (Push.Local.sumBudget_mul_left (estate.suggests o) non) ?_ ?_ le_rfl
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth estate.positive _).le (norm_nonneg _)) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    by_cases h : (M i).center=o
    · simp only [if_pos h]
      have row := entry M w grades estate hs x A hc axis gp i
      calc
        _ ≤ Poly.toll w (M i).mode * ((M i).salary*tariff G σ cap g p shelf)*Real.exp (σ*(M i).length) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left row (Poly.worth estate.positive _).le) (Real.exp_pos _).le
        _ = _ := by unfold Row.height; ring
    · simp [h]

private theorem modeBill (s : Γ.Mode) :
    SumBudget (fun i => Poly.toll w s * ‖if (M i).mode=s then error (M i) x g A p else 0‖)
      (tariff G σ cap g p shelf*((s.val.image P.origin).card*c)) := by
  have non : 0 ≤ tariff G σ cap g p shelf := by unfold tariff; positivity
  have pay := WilsonFirstReceivedIssuedIncome.salary M w estate.positive hs.le estate.suggests s
  refine Push.PriceCompiler.sumBudget_mono (Push.Local.sumBudget_mul_left pay non) ?_ ?_ le_rfl
  · intro i; exact mul_nonneg (Poly.worth estate.positive _).le (norm_nonneg _)
  · intro i
    by_cases hit : (M i).mode=s
    · simp only [if_pos hit]
      refine (mul_le_mul_of_nonneg_left (entry M w grades estate hs x A hc axis gp i) (Poly.worth estate.positive s).le).trans_eq ?_
      ring
    · simp [hit]

omit [DecidableEq V] estate hs hc axis gp in
private theorem gradesSum (g : ℂ) (D : Finset ℕ) (f : ℕ → ι → ℂ) (e : ℕ → ℂ)
    (h : ∀ j ∈ D, HasSum (f j) (e j)) :
    HasSum (fun i => ∑j ∈ D,g^j*f j i) (∑j ∈ D,g^j*e j) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert j D hj ih =>
    simpa only [sum_insert hj] using
      ((h j (mem_insert_self ..)).mul_left (g^j)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))


theorem original (layout : Layout G) (tape : Finset Age) (s : Γ.Mode) :
    let issued := Air.craft M (fun i => (M i).paint x) grades layout tape
    let angle := arm G n 1 A
    let value := (Integral.markedLog g (Integral.sample g angle) issued).part s
    let filed := (WilsonCoherentMayerWindingGrades.panel p (g:ℂ) (fun j => Air.discharge issued j angle)).part s
    Poly.toll w s * ‖value-filed‖ ≤ tariff G σ cap g p shelf*((s.val.image P.origin).card*c) := by
  intro issued angle value filed
  letI : Fintype V := Fintype.ofInjective Γ.fire (fun a b h => (Γ.fire_inj a b).mp h)
  let κ := Poly.toll w s
  let y := Integral.sample g angle
  let ink (i : ι) := (M i).paint x
  let roster := Air.license M ink grades w estate hs (fun i => estate.honor i x)
  let fy (i : ι) := if (M i).mode=s then (M i).nominal g x y else 0
  let fj (j : ℕ) (i : ι) := if (M i).mode=s then ink i * ((M i).markReceipt j A : ℂ) else 0
  let z (i : ι) := if (M i).mode=s then error (M i) x g A p else 0
  have live : 0 < κ := Poly.worth estate.positive s
  have unmasked : HasSum fy value := by
    apply (Pi.hasSum.mp (Air.liftPassport M ink grades roster layout tape g gp.ne' y) s).congr_fun
    intro i
    change fy i = (Poly.send (M i).mode _).part s
    rw [Poly.part_send]
    by_cases h : (M i).mode=s <;> simp [fy,h,eq_comm,Air.grainR,ink,Row.nominal]
  have readings (j : ℕ) : HasSum (fj j) ((Air.discharge issued j angle).part s) := by
    apply (Pi.hasSum.mp (Air.compared M ink grades roster layout tape A j) s).congr_fun
    intro i
    change fj j i = (Poly.send (M i).mode _).part s
    rw [Poly.part_send]
    by_cases h : (M i).mode=s <;> simp [fj,h,eq_comm]
  have sum := gradesSum (g:ℂ) (range (p+1)) fj (fun j => (Air.discharge issued j angle).part s)
    (fun j _ => readings j)
  have weighted : HasSum z (value-filed) := by
    have sl : filed = ∑j ∈ range (p+1),(g:ℂ)^j*(Air.discharge issued j angle).part s := by
      simp only [filed,WilsonCoherentMayerWindingGrades.panel,Poly.part_sum,Poly.part_smul]
    rw [sl]
    apply (unmasked.sub sum).congr_fun
    intro i
    by_cases h : (M i).mode=s <;> simp [z,fy,fj,ink,error,h,y,angle]
  have income := modeBill M w grades estate hs x A hc axis gp s
  have summable : Summable fun i => ‖z i‖ := by
    simpa only [←mul_assoc,inv_mul_cancel₀ live.ne',one_mul,z,κ] using (income.2.1.mul_left κ⁻¹)
  rw [← weighted.tsum_eq]
  calc
    _ ≤ κ*(∑' i, ‖z i‖) := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm summable) live.le
    _ = ∑' i, κ*‖z i‖ := tsum_mul_left.symm
    _ ≤ _ := income.2.2

end YM.Integration.WilsonReceivedSourceRoster
