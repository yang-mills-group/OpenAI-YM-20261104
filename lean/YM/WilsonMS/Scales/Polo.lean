import YM.WilsonMS.Scales.Floating
/-!
# Pure powers/logs exclude nontrivial filtered spill after scaling

Elementary argument: collect first power where filtration can spill and
note adjoint of exponential tends to projection; the polynomial across
scales would have to be constant, so tangent of spill vanishes. No bound
on anomalous dimensions is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G

def Lines (P : ChartK G d) :=
  ∀ n x, x ∈ conf n → ∀ v i, Ready (fun s => sweep s P n x i v)
variable {F K : ChartK G d} {P Q B : Guard G d}

private lemma point_budget {u : ℝ → ChartK G d} {x : Points n}
    (h : ∀ i v, Ready (fun s => u s n x i v)) (P : Guard G d) :
    ∀ i v, Ready (fun s => Act (u s) P n x i v) := by
  intro i v
  unfold Act
  simp_rw [pivot_cost]
  exact accounts _ fun i _ => h _ _
namespace Lines

lemma pulls (h : Lines F) (hp : Mass P) : Lines (Act F P) := by
  intro n x hx p i
  simp_rw [adjoint, paceM _ hp]
  exact point_budget (u := fun s => sweep s F) (fun i v => h n x hx v i) _ _ _

lemma subs (h : Lines F) {c : Cn} (hp : Rooted c) : Lines (Sub c F) := by
  intro n x hx p i
  simp_rw [← name_sub _ hp]
  unfold Sub
  simp_rw [bookCost, rules, smul_eq_mul]
  exact
    accounts (Finset.Iic i) fun v _ =>
      Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (Ready.const _) (h _ _ hx p v)

lemma spun (h : Lines F) (t : ℝ) : Lines (sweep t F) := by
  intro n x hx v N
  simp_rw [lands]
  exact plus_poly (h _ _ hx _ _) t

lemma pass (p : Equad F K) (h : Lines F) : Lines K := by
  intro n x hx v i
  simp_rw [show ∀ t : ℝ, sweep t K n x = sweep t F n x from fun t => (sweep_t p t n hx).symm]
  exact h _ _ hx v i
end Lines

lemma global_P {A : Booked (Ensure.deck G)} (F : MS_Data G A) (μ : ℝ) : Lines (GMS F μ d) := by
  intro n x hx v N
  simp_rw [show ∀ r : ℝ, sweep r (GMS F μ d) n x = GMS F (μ - r) d n x from fun r =>
      starClock F μ r d n hx]
  apply coord_burn (F := fun t => GMS F t d n x N v) _ μ
  unfold GMS
  let B := Daylight BΨ d
  have ht (Q : Point G d n) :
    Q v = ∑ j : Fin n → Glyph BΨ d, (∏ i, B.coord (j i) (v i)) * Q (glow ∘ j) := fromHeight ..
  simp_rw [ht (lowKernel F _ _ _ _), lowK]
  apply accounts
  intro i hi
  refine Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (Ready.const _) ?_
  let h :=
    group_visit (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx) 0
      (fun _ : Unit => Set.mem_singleton x)
  obtain H := TraceMC.letLog h F (profileK i) Finset.univ N
  exact H.linear (LinearMap.proj ())

lemma point_jump {a : Days n} (ha : a ∈ Normalize.tally j n) (v : Option (Fin n)) (hp : a v = j) :
    a = Finsupp.single v j := by
  ext1 i
  by_cases h : i = v
  · subst i
    rw [hp, Finsupp.single_eq_same]
  rw [Finsupp.single_eq_of_ne h]
  have he := (totaled a).mp ha
  rw [← Finset.add_sum_erase Finset.univ (fun i => a i) (Finset.mem_univ v), hp] at he
  have hh : ∑ i ∈ Finset.univ.erase v, a i = 0 := by omega
  exact
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hh i
      (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)

def wages (P : Point G d n) (T : FieldEnd G d) (p : Fin n → Sec G d) :=
  ∑ i : Fin n, P (update p i (T (p i)))

lemma forces {x : Points n} (v : Fin n → Sec G d) (F : ChartK G d) (hj : j ≠ 0) (hP : CloseP P)
    (hQ : CloseP Q) (ht : ∀ n < j, coeff n P = coeff n Q) :
    Act F P n x j v - Act F Q n x j v = wages (F n x 0) (coeff j P - coeff j Q) v := by
  unfold Act
  rw [pivot_cost, pivot_cost, ← Finset.sum_sub_distrib]
  let a (k : Days n) := F n x (k none) (pulseU k P v) - F n x (k none) (pulseU k Q v)
  let J := jumpDay n j
  let B := Finset.univ.image J
  have he : B ⊆ Normalize.tally j n := by
    rintro i hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    exact jumping ..
  rw [← Finset.sum_subset he (f := a) ?_,
    Finset.sum_image (f := a) (g := J) ((Normalize.jumper hj).injOn)]
  swap
  · intro i hi h
    unfold a
    apply sub_eq_zero.mpr
    apply congr_arg
    funext k
    unfold pulseU
    rw [ht _ ?_]
    apply
      lt_of_le_of_ne
        ((Finset.single_le_sum (f := fun j => i j) (fun j _ => Nat.zero_le _)
              (Finset.mem_univ (some k))).trans_eq
          ((totaled i).mp hi))
        (fun hm =>
          h ((point_jump hi (some k) hm).symm ▸ Finset.mem_image_of_mem J (Finset.mem_univ k)))
  exact
    Finset.sum_congr rfl fun i _ => by
      simp_rw [a, J, Normalize.drift, hP.zeroC, hQ.zeroC, LinearMap.sub_apply,
        MultilinearMap.map_update_sub, jumpDay,
        Finsupp.single_eq_of_ne (show none ≠ some i from (Option.some_ne_none _).symm)]
      rfl

lemma power_mass (hc : G.Simple) (h : CloseP P) (hF : Lines F) (hv : Lines (Act F P))
    (ht : ∀ (t : ℝ) n x, x ∈ conf n → sweep t F n x 0 = Normalize.scene x d) : Mass P := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 0
    · subst n
      rw [(printH h).zeroC, h.zeroC]
    let T : Change G d :=
      ⟨coeff n P - coeff n (printM P),
        @Submodule.sub_mem ℝ (FieldEnd G d) _ _ _ (Change G d) _ _ (positiveC h he)
          (positiveC (printH h) he)⟩
    suffices hx : T = 0 by exact Eq.symm (sub_eq_zero.mp (congr_arg Subtype.val hx))
    apply Normalize.normstab hc T
    rw [Normalize.genre]
    intro k x hx v
    let X t := sweep t F
    let A t := Act (X t) (buryD t P)
    let B t := Act (X t) (printM P)
    let U (t : ℝ) := A t k x n v - B t k x n v
    have hμ : Ready U :=
      Ready.sub
        (show Ready (fun t => A t k x n v) from
          (by
            rw [show A = (fun t => sweep t (Act F P)) from funext fun t => Eq.symm (adjoint ..)]
            exact hv k x hx v n))
        (point_budget (u := X) (fun i w => hF _ _ hx w i) _ _ v)
    have hS (s : ℝ) : U s = wages (scene x d) (coeff n (buryD s P) - coeff n (printM P)) v := by
      change Act (X s) _ _ _ _ v - Act _ _ _ _ _ _ = _
      rw [forces v _ he (duties s h) (printH h) ?_, show X s k x 0 = _ from ht _ _ _ hx]
      intro i hi
      exact (on_time s ((printed _ |>.symm.trans (ih i hi)) : Flat (coeff i P))).trans (ih i hi).symm
    have Ht : Tendsto U atTop (𝓝 0) := by
      rw [funext hS]
      unfold wages
      rw [show (0 : ℂ) = ∑ _i : Fin k, (0 : ℂ) from (Finset.sum_const_zero).symm]
      refine tendsto_finsetSum _ fun i _ => ?_
      let L := (scene x d (G := G)).toLinearMap v i
      let p := v i
      let q := L (coeff n (printM P) p)
      change Tendsto (fun s => L ((coeff n (buryD s P) - coeff n (printM P)) p)) _ _
      simp_rw [LinearMap.sub_apply, map_sub]
      rw [← show q - q = 0 from sub_self _]
      exact (exchange_cost h L n p).sub tendsto_const_nhds
    have hz := congr_fun (quiet hμ Ht) 0
    rw [hS 0, buryD, neg_zero, walk_o, one_mul, mul_one] at hz
    exact hz
end YM.WilsonMS.GFlow
