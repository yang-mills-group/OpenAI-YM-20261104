import YM.Integration.WilsonTrueProjectedLocatedBasis
import YM.Integration.WilsonTrueProjectedPointStock
import YM.Integration.WilsonTrueProjectedNaturalFee

/-! Sum the actual basis quotes after restoring the one power already
paid by each dated source. The estimate holds at every intermediate
displaced parent on the same cutoff program. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedSalary
open Function Filter Finset PowerSeries Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PhysicalNext Repeat Legato RemainderComparison ConnectedActivityE6 Push
open WilsonTrueProjectedPointInverse WilsonTrueProjectedPointProgram WilsonPinnedWidthTransport
open WilsonTrueProjectedCourse WilsonOriginalNullCorridor
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "C₀" => R.family
local notation "ι" => Letter (R.family.labels.level d)
local notation "Λ" => RG16.Lambda R.family.path.levels

theorem restore {E : Type*} [Fintype E] (q earned : ℕ) {g B A : ℝ} (positive : 0 < g)
    (hB : 0 ≤ B) (x : Fin (q+1) → E → ℂ) (u : Fin (q+1) → E → ℝ)
    (stock : ∀ k, (∑ b,‖x k b‖) ≤ A*g^k.val)
    (seat : ∀ k b,u k b ≤ B*g^(earned+1)) :
    (∑ k : Fin (q+1), ∑ b, (‖x k b‖/g^k.val)*u k b) ≤ (q+1:ℕ)*A*B*g^(earned+1) := by
  have grades (k : Fin (q+1)) : (∑ b, (‖x k b‖/g^k.val)*u k b) ≤ A*(B*g^(earned+1)) := by
    calc
      _ ≤ ∑ b, (‖x k b‖/g^k.val)*(B*g^(earned+1)) :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (seat k b) (by positivity)
      _ = ((∑ b,‖x k b‖)/g^k.val)*(B*g^(earned+1)) := by rw [←sum_mul,sum_div]
      _ ≤ A*(B*g^(earned+1)) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos positive _)).mpr (stock k)) (by positivity)
  calc
    _ ≤ ∑ _ : Fin (q+1), A*(B*g^(earned+1)) := sum_le_sum fun k _ => grades k
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem decay_sum {δ : ℝ} (gap : δ < 1/8) (b i n : ℕ) :
    (∑ t ∈ range n, gain C₀ (b+i) (b+i+t)*Real.exp (δ*elapsed (C₀).S b (b+i+t))) ≤
      (1-(3:ℝ)^(δ-1/8))⁻¹ * Real.exp (δ*elapsed (C₀).S b (b+i)) := by
  let ρ := (3:ℝ)^(δ-1/8)
  have hp : 0 ≤ ρ := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr gap)
  have piece (t : ℕ) : gain C₀ (b+i) (b+i+t)*Real.exp (δ*elapsed (C₀).S b (b+i+t)) ≤
      ρ^t*Real.exp (δ*elapsed (C₀).S b (b+i)) := by
    rw [gain,←Real.exp_add,show ρ^t = Real.exp (((t:ℝ)*Real.log 3)*(δ-1/8)) by
      dsimp only [ρ];rw [Real.rpow_def_of_pos (by norm_num),←Real.exp_nat_mul];congr 1;ring,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_right (blocks (C₀).S (b+i) t) (sub_nonpos.mpr gap.le)
    unfold elapsed at h ⊢
    linarith only [h]
  calc
    _ ≤ ∑ t ∈ range n, ρ^t*Real.exp (δ*elapsed (C₀).S b (b+i)) := sum_le_sum fun t _ => piece t
    _ = (∑ t ∈ range n,ρ^t)*_ := by rw [sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have s := hasSum_geometric_of_lt_one hp h1
      exact (s.summable.sum_le_tsum _ (fun _ _ => pow_nonneg hp _)).trans_eq s.tsum_eq

variable (wood : Primer.Families R.family) (a : hue G) (depth : d<D)

theorem original (simple : G.Simple) (o : Stationary.Loc G 1) {U : ℕ → ℕ}
    (formal : WilsonWindowFormalPurchase.Canonical U R.kit)
    (point : WilsonNeutralPointForecast.Filed R.kit) (weakly : WilsonNeutralPointWeakForecast.Filed R.kit)
    (slow : ∀ i,(((C₀).S.block i).val:ℝ) ≤ Real.log (Λ i))
    (q earned target : ℕ) (head : target+2 ≤ earned+1) {δ : ℝ} (positive : 0<δ) (gap : δ<1/8) :
    ∃ K : ℝ, ∃ V : ℕ, 0<K ∧ ∀ᶠ b : ℕ in atTop,
    ∀ (_ : d≤(C₀).path.levels.clock.J (b+1)) (digit : ∀ j,Site ((C₀).S.block j))
      (N per stop i n : ℕ), b+i+n ≤ stop → stop ≤ N →
    ∀ (report : ι → ℂ) (origin fare : ℝ), 0≤origin → 0≤fare → (∀ t,‖report t‖≤origin) →
    ∀ (u : ℕ → Fin (q+1) → ι → ℝ),
    let g := fun j => Coat.gStep (((C₀).path.rep N per j).beta)
    let top := take R q (lift R wood a depth digit N b g (fun l => PowerSeries.C (report l)) (stop-b))
    let X := income R wood a depth digit N stop q g top
    let bill := fun j => ∑ k : Fin (q+1), ∑ l, (‖X (j+1) k l‖/(g j)^k.val)*u j k l
    (∀ j≥b+i, j<b+i+n → ∀ k l, u j k l ≤ fare*(g j)^(earned+1)) →
    (∑ t ∈ range n,gain C₀ (b+i) (b+i+t)*((2+4*Trace.Physical.GermGraph.stock C₀ (b+i+t))*bill (b+i+t))) ≤
      K*(Λ b)^V*origin*fare*power R target b*Real.exp (δ*elapsed (C₀).S b (b+i)) := by
  classical
  obtain ⟨C,V,hC,stocked⟩ := WilsonTrueProjectedPointStock.original R wood a depth simple o formal point weakly q positive
  obtain ⟨start,calendar⟩ := eventually_atTop.mp (WilsonTrueProjectedNaturalFee.calendar R simple slow 0 earned target (by omega))
  let gainCap := (1-(3:ℝ)^(δ-1/8))⁻¹
  have capPositive : 0 < gainCap := inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr gap)))
  refine ⟨((q+1:ℕ):ℝ)*C*(10*2^(earned+1))*gainCap,V,by positivity,?_⟩
  filter_upwards [stocked,Filter.eventually_ge_atTop start] with b receipts active
  intro front digit N per stop i n horizon roof report origin fare hO hF bound u
  dsimp only
  intro fees
  let g := fun j => Coat.gStep (((C₀).path.rep N per j).beta)
  let top := take R q (lift R wood a depth digit N b g (fun l => PowerSeries.C (report l)) (stop-b))
  let X := income R wood a depth digit N stop q g top
  let bill := fun j => ∑ k : Fin (q+1), ∑ l, (‖X (j+1) k l‖/(g j)^k.val)*u j k l
  let M := ((q+1:ℕ):ℝ)*C*(Λ b)^V*origin*fare*(10*2^(earned+1))*power R target b
  have lam : 0 ≤ Λ b := zero_le_one.trans (WilsonTrueProjectedPointClock.log_rise R simple (le_refl b)).1
  have base : 0 ≤ power R target b := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have m0 : 0 ≤ M := by dsimp only [M];positivity
  have paid (j : ℕ) (entered : b+i ≤ j) (upper : j < b+i+n) :
      (2+4*Trace.Physical.GermGraph.stock C₀ j)*bill j ≤ M*Real.exp (δ*elapsed (C₀).S b j) := by
    obtain ⟨coupling,tariff⟩ := calendar j (by omega) N per (by omega)
    simp only [pow_zero,mul_one] at tariff
    have age := receipts front digit N per stop j (by omega) (by omega) roof report origin hO bound
    have combined := restore q earned coupling hF (X (j+1)) (u j) age (fees j entered upper)
    have growth := Real.exp_pos (δ*elapsed (C₀).S b j)
    have book : 0 ≤ Trace.Physical.GermGraph.stock C₀ j := by
      exact zero_le_one.trans (stage C₀ j).columns_ge
    have monotone : power R target j ≤ power R target b :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_left _ _))
        (max_le_max_left 1 (WilsonTrueProjectedPointClock.monotone R simple (by omega)))
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))
    calc
      _ ≤ (2+4*Trace.Physical.GermGraph.stock C₀ j)*(((q+1:ℕ):ℝ)*(C*(Λ b)^V*origin*Real.exp (δ*elapsed (C₀).S b j))*fare*(g j)^(earned+1)) :=
        mul_le_mul_of_nonneg_left combined (by positivity)
      _ = (((q+1:ℕ):ℝ)*C*(Λ b)^V*origin*fare*Real.exp (δ*elapsed (C₀).S b j))*
        ((2+4*Trace.Physical.GermGraph.stock C₀ j)*(g j)^(earned+1)) := by ring
      _ ≤ (((q+1:ℕ):ℝ)*C*(Λ b)^V*origin*fare*Real.exp (δ*elapsed (C₀).S b j))*
        ((10*2^(earned+1))*power R target b) :=
        mul_le_mul_of_nonneg_left (tariff.trans (mul_le_mul_of_nonneg_left monotone (by positivity))) (by positivity)
      _ = _ := by dsimp [M];ring
  calc
    _ ≤ ∑ t ∈ range n,gain C₀ (b+i) (b+i+t)*(M*Real.exp (δ*elapsed (C₀).S b (b+i+t))) :=
      sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (paid _ (by omega) (by have := mem_range.mp ht;omega))
        (Real.exp_pos _).le
    _ = M*(∑ t ∈ range n,gain C₀ (b+i) (b+i+t)*Real.exp (δ*elapsed (C₀).S b (b+i+t))) := by
      rw [mul_sum];exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ M*(gainCap*Real.exp (δ*elapsed (C₀).S b (b+i))) :=
      mul_le_mul_of_nonneg_left (decay_sum R gap b i n) m0
    _ = _ := by dsimp only [M];ring

end YM.Integration.WilsonTrueProjectedLocatedSalary
