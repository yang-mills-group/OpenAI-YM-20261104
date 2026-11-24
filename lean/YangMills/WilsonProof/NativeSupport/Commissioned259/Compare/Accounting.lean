import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Rate
/-!
# From G.1 and G.9 input prices to the first line of M.2: the computation

This module does the *full row* algebra/analysis with explicit genuine operands of the prediction.
Parametric on the given hypothesis for genuine correlation (use for G.9 on exact H_r fields)
and on genuinely paid high power **conversion errors** (`G.1`). For one set of slots; use twice
with different arities. The error theorem is eventual on any parameterized spaces simultaneously
obeying the moving hypotheses. Use to obtain uniform control for T growing all the way to the
price budget, see the physical application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m h : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ → PowerSeries ℂ}
    {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ h) (he : ∀ i, e i ≤ h)

abbrev Response (G : Gauge) (d : Fin n → ℕ) (e : Fin m → ℕ) :=
  MultilinearMap ℂ (fun i ↦ Sec G (d i)) (MLA G e)

-- Note `_` parameters let dims vary. Receive full row with same labels unmarked.
def reading (V : Arenas G) {d : Fin n → ℕ} {e : Fin m→ℕ} (hd : ∀ i, d i ≤ h) (he : ∀ i, e i ≤ h)
    (x : Points n) (y : Points m) (p : ℕ) (t : ℝ) : Response G d e :=
  ∑ k ∈ Finset.range (p+1), (t:ℂ)^k • bareRow V hd he x y k

def expansion (V : Arenas G) (B : ℝ→Frames G) {d : Fin n → ℕ} {e : Fin m→ℕ}
    (hd : ∀ i, d i ≤ h) (he : ∀ i, e i ≤ h) (x : Points n) (y : Points m) (η : ℝ) (p : ℕ) (t : ℝ) : Response G d e :=
  ∑ k ∈ Finset.range (p+1), (t:ℂ)^k • inserted V B hd he x y η k

section
variable (p : ℕ) (η t : ℝ) (x : Points n) (y : Points m) (u : Slots G d) (v : Slots G e)
lemma read_eq : reading V hd he x y p t u v = crop p t (mk fun k=>bareRow V hd he x y k u v) := by
  simp_rw [reading,crop_apply,_root_.sum_apply,_root_.smul_apply,coeff_mk,smul_eq_mul]
lemma expansion_eq : expansion V B hd he x y η p t u v = crop p t (measurement V B hd he x y η u v) := by
  simp_rw [expansion,measurement,crop_apply,_root_.sum_apply,_root_.smul_apply,coeff_mk,smul_eq_mul]

lemma read_basis (P : O.Score.Regular V) (b : BasisSlots G d) (q : BasisSlots G e) :
    (mk fun k=>bareRow V hd he x y k (word b) (word q)) = party (install V) x y (names b) (names q) := by
  ext1 k; rw [coeff_mk]; exact bareEntry P hd he x y (included b) (included q) k

/-- Size-horizon-unrestricted coordinate version of `measured_basis`, useful where v
is a vector: sum powers also on differing caps, then use K's actual structure for costs. -/
lemma all_components : measurement V B hd he x y η u v = ∑ q : BasisSlots G e,
    (∏ i, badge B η (v i) (q i)) * mk (fun k=>bareRow V hd he x y k u (word q)) := by
  ext1 k; simp_rw [map_sum, measurement, Constants.admits, coeff_mk, inserted_apply, badge, coeff_mk]
  rw [Finset.sum_comm (s:= Finset.univ)]
  exact Finset.sum_congr rfl fun i hi=> word_sigma (kSlots B η i v) _
end

abbrev adjusted (A : (i : Fin m) → Module.End ℂ (Sec G (e i))) (Y : Response G d e) : Response G d e :=
    (MultilinearMap.compLinearMapₗ A).compMultilinearMap Y
@[simp]
lemma adjusted_apply (A : (i : Fin m) → Module.End ℂ (Sec G (e i))) (Y : Response G d e) (u) (v) :
    adjusted A Y u v = Y u (fun i=> A i (v i)) := rfl

variable {I : Type*} {X : Filter I} {T t g : I → ℝ} (hT : ∀ᶠ i in X, 1 ≤ T i)

-- Power budget on T-arguments along synchronized geometry
include hT in
lemma offPay (u : ℕ) (b : I→ℝ) : b =O[X] (fun i => (T i)^u * b i) := by
  refine IsBigO.of_bound' ?_; filter_upwards [hT] with i hi; rw [norm_mul,norm_pow,Real.norm_of_nonneg (zero_le_one.trans hi)]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hi)

include hT in
lemma fall (a : ℕ) : (fun i=> ((T i)⁻¹)^a) =O[X] fun i=> (1:ℝ) := by
  refine IsBigO.of_bound' ?_; filter_upwards [hT] with i hi
  have ht := zero_lt_one.trans_le hi
  rw [norm_pow, norm_inv, Real.norm_of_nonneg ht.le,norm_one]; exact pow_le_one₀ (by positivity) ((inv_le_one₀ ht).mpr hi)

/- General application from responses on only the fixed basis tuples to the amplitudes.
Never estimates w-cost on inverse operations from a history crossing position. -/
include hT in
lemma applying {F : I→Response G d e} (w : I → ℝ)
    (hf : ∀ u v, Fare T X w (fun i=> F i (word u) (word v)))
    {u : I → Slots G d} {v : I→ Slots G e} (hu : ∀ q, Fare T X (fun _=>1) (fun i=> coordinates q (u i)))
    (hv : ∀ q, Fare T X (fun _=>1) (fun i=> coordinates q (v i))) : Fare T X w (fun i=> F i (u i) (v i)) := by
  simp_rw [word_sigma (u _) (F _),_root_.sum_apply,_root_.smul_apply, word_sigma (v _),smul_eq_mul]; exact
    Fare.sum hT fun _ _=>Fare.cover (hu _) (Fare.sum hT fun j _=> Fare.cover (hv j) (hf _ j))

section Rates
variable (L : Law V R B) (P : O.Canon.Physical V R B)
    {W : ℝ} {K : Set (Points n)} {S : Set (Points m)} (hK : IsCompact K) (hx : K⊆conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (hW : 1 ≤ W) (hz : clears W K S)
    {x : I → Points n} (hu : ∀ᶠ i in X, x i∈K) {y : I→Points m} (hv : ∀ᶠ i in X, y i∈S) (hi : ∀ᶠ i in X,W ≤ T i)
    (ht : ∀ᶠ i in X, |t i| ≤ 1) (paid : t=O[X] g) (hg : ∀ᶠ i in X, |g i| ≤ 1)
    (F : I → Response G d e)
    (A : I → (i : Fin m) → Module.End ℂ (Sec G (e i)))
local notation "DE" => ∑ i,e i
local notation "cost" => (fun i:I=> T i^DE)
local notation "η" => (fun i:I=> -Real.log (T i))

variable (p : ℕ) (q : Fin m→ℕ) (hq : ∀ i,p≤q i)
local notation "predict" => fun i:I => reading V hd he (x i) (T i • y i) p (t i)
local notation "finalRow" => fun i:I => expansion V B hd he (x i) (T i • y i) (η i) p (t i)
local notation "FT" => (fun i:I=> cost i*g i^(p+1))
variable
    -- G.1 norms restated on components.
    (norms : ∀ (i : Fin m) (b z : Toon G (e i)),
      (fun r => coord z (A r i (theory b))) =O[X] (fun r=> T r^(e i)))
    (reports : ∀ (i : Fin m) (b z : Toon G (e i)),
      (fun r => coord z (A r i (theory b))-crop (q i) (t r) (badge B (-Real.log (T r)) (theory b) z)) =O[X] (fun i=>g i^(p+2)))

include norms
lemma precomposed (f : I→Response G d e) (u : BasisSlots G d) (hf : ∀ v,
    Fare T X (fun i=>g i^(p+1)) (fun i=> f i (word u) (word v))) (v : BasisSlots G e)
    (hT : ∀ᶠ i in X, 1 ≤ T i) : Fare T X FT (fun i=> adjusted (A i) (f i) (word u) (word v)) := by
  simp_rw [adjusted_apply, word_sigma (fun r => A _ r _) (f _ (word u)), coordinates, smul_eq_mul]
  refine Fare.sum hT fun b _=> ((Fare.prod (fun j (_: j ∈ (Finset.univ:Finset (Fin m)))=> Fare.bare (norms j (v j) (b j)))).mul (hf b)).extend ?_
  exact Eventually.of_forall fun i=>by rw [Finset.prod_pow_eq_pow_sum]

include hq reports paid P L hi hW hu hv hz hy hS hx hK ht hg
/-- Substitute the genuine reports into the predictor and pay both replacements and all missing
powers. The latter price actually independent of T except powers of logs. -/
lemma replacing (u : BasisSlots G d) (v z : BasisSlots G e) :
    let K (j:Fin m) i:= badge B (η i) (word v j) (z j)
    let Y i:= party (install V) (x i) (T i • y i) (names u) (names z)
    Fare T X FT (fun i=> (∏ j, coord (z j) (A i j (word v j))) * crop p (t i) (Y i) -
      (∏ j:Fin m, crop (q j) (t i) (K j i))*crop p (t i) (Y i)) ∧
    Fare T X (fun i=>g i^(p+1)) (fun i=> (∏ j:Fin m, crop (q j) (t i) (K j i))*crop p (t i) (Y i)-
      crop p (t i) ((∏ j,K j i)*Y i)) := by
  intro Kz Y
  have hT := hi.mono fun i h=> hW.trans h
  let w := totalG (names z)
  let D (j:Fin m) (i:I) := T i^(heft (flash (z j)))
  let w' (i:I) := ((T i)⁻¹)^w
  have hY : Tunes T X w' Y := whole_full P hK hx hS hy hW hz (names u) (names z) hu hv hi
  have hZ (i: Fin m) : Tunes T X (D i) (Kz i) := badge_cost L hT (word v i) (z i)
  have hmk := Tunes.cuts hT ht p hY
  constructor
  · let a (j: Fin m) (i : I) := coord (z j) (A i j (word v j))
    let k (j: Fin m) (i : I) := crop (q j) (t i) (Kz j i)
    let W (j: Fin m) (i : I) := T i^(e j)
    have hh (j) : Fare T X (W j) (a j) := Fare.bare (norms j ..)
    have hc (j) : Fare T X (W j) (k j) := by
      refine (Tunes.cuts hT ht (q j) (hZ j)).transport (IsBigO.of_bound' ?_)
      filter_upwards [hT] with i hi; unfold D W; rw [norm_pow,norm_pow]; exact pow_le_pow_right₀ (hi.trans (le_abs_self _)) (size_le _)
    have hd (j) : Fare T X (fun i=>g i^(p+1)* W j i) (fun i=> a j i-k j i) := by
      refine Fare.bare (((reports j (v j) (z j)).trans (Fare.over_pow (p+1) (p+2) (by omega) X g hg)).trans (show (fun i=>g i^(p+1)) =O[X] (fun i=>g i^(p+1)* W j i) from
        (offPay hT (e j) (fun i=>g i^(p+1))).congr_right fun i=> mul_comm ..))
    simp_rw [ ← sub_mul ]
    refine ((Fare.overall hT (s:=Finset.univ) (fun j _=>hh j) (fun j _=>hc j) (fun j _=> hd j)).mul (hmk.transport (fall hT w))).extend ?_
    exact Eventually.of_forall fun i=> by unfold W; rw [Finset.prod_pow_eq_pow_sum,mul_one,mul_comm]
  refine (Tunes.overrun hT ht paid p Finset.univ q (fun i _=>hq i) D Kz (fun i _=>hZ i) hY).extend ?_
  filter_upwards [hT] with i hi
  unfold D w'
  rw [Finset.prod_pow_eq_pow_sum]
  change g i ^ (p+1) * (T i ^ w * _)=_
  rw [←mul_pow,mul_inv_cancel₀ (by linarith),one_pow,mul_one]

/- G.9 here is consumed on *ordinary, unmarked* reads with all inputs H_r, needs hold
only for a finite set of basis requests. We show M.2 first-line price. -/
variable (G9 : ∀ u v, Fare T X (fun i=>g i^(p+1)) (fun i=>
    F i (word u) (word v) - reading V hd he (x i) (T i • y i) p (t i) (word u) (word v)))
include G9
lemma first_line (u : BasisSlots G d) (v : BasisSlots G e) : Fare T X FT (fun i=>
    adjusted (A i) (F i) (word u) (word v) - finalRow i (word u) (word v)) := by
  have hT := hi.mono fun i h=> hW.trans h
  have h := precomposed (T:=T) A p norms (fun i=>F i-predict i) u (G9 u) v hT
  have ht0 : Fare T X FT (fun i=> adjusted (A i) (predict i) (word u) (word v) -
      finalRow i (word u) (word v)) := by
    simp_rw [adjusted_apply, word_sigma (fun r=> A _ r _) (predict _ (word u)), read_eq,
      expansion_eq, all_components, read_basis hd he _ _ P.dimensions, map_sum, coordinates, smul_eq_mul,
      ← Finset.sum_sub_distrib]
    refine Fare.sum hT fun j _=> ?_
    obtain ⟨L,H⟩ := replacing L P hK hx hS hy hW hz hu hv hi ht paid hg A p q hq norms reports u v j
    exact (Fare.add hT L (H.transport (offPay hT DE _))).congr (Eventually.of_forall fun i=>by dsimp only; abel)
  exact (Fare.add hT h ht0).congr (Eventually.of_forall fun i=>by
    simp only [adjusted_apply,_root_.sub_apply]; abel)
end Rates
end YM.FVA2.GradedFar259.Comparing
