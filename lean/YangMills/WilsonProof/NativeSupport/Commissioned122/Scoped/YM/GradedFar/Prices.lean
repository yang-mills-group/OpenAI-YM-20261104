import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Expansion
import YM.FVA2.O.Canon.Docket
/-!
# F.O, F.1, and grading cancellation

`Physical` below is **only** the original predicate on the formal kernel book.
Use the wilson projection from Match of the same independent formal construction.
FAR means first remove the independent regulator. No cutoff mesh price is being
stretched to these configurations. We use the RangeP, PaceX and ChargeP inputs
(from Match as in WiderProfiles.separate_predictor_inputs), not wider profile
θ-prices here. Retain also the price for the *whole uncorrected* homogeneous
row. Then the basis-expansion proof on every Far leg; use Match.dilation too in
applying that result (law argument).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set Scale O O.Score O.Enh O.Read O.Project O.Canon PowerSeries
open XSpace XSpace.Normalize Dframe MS.Book.Program
open scoped Classical Topology BigOperators

variable {G : Gauge} {H h k p n m : ℕ} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ}
    {B : ℝ → Frames G} (phys : Canon.Physical V ψ B)

lemma post_log {T : ℝ} (ht : 0 < T) (k a : ℕ) :
    post k (Real.log T) a = (1+Real.log T)^a * (T^k)⁻¹ := by
  unfold post; rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ht]

lemma toSpatial {I E : Type} [NormedAddCommGroup E] {f : I → ℝ → E} (k : ℕ)
    (rain : Rain (k:ℝ) f) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
      ∀ i, ‖f i (Real.log T)‖ ≤ C*(1+Real.log T)^a * (T^k)⁻¹ := by
  obtain ⟨C,hC,j,h⟩ := rain; refine ⟨C,hC,j,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually h] with T ht hw
  intro i; rw [mul_assoc, ← post_log ht]; exact hw i

lemma squeeze_log {T : ℝ} (ht : 0 < T) (y : Points m) : squeeze (-Real.log T) y = T • y := by
  rw [squeeze, neg_neg, Real.exp_log ht]

variable {K : Set (Points n)} {S : Set (Points m)}
    (kc : IsCompact K) (hk : K ⊆ conf n) (sc : IsCompact S) (hs : S ⊆ Outside m)
    (u : Scan G n) (v : Scan G m) (q : Q G)

include kc hk in
lemma configurations (sc : IsCompact S) (hs : S ⊆ Outside m) :
    ∀ᶠ T in (atTop : Filter ℝ), ∀ x ∈ K, ∀ y ∈ S,
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) := by
  filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually (for_far kc hk sc hs)]
    with T hT hw x hx y hy
  rw [← squeeze_log hT]; exact ⟨hw x hx y hy, lives _ (hs hy)⟩

/-## Recover the homogeneous inputs on this alphabet. -/
local notation "V0" => install V
include phys
include kc hk sc hs in
lemma FO_basis (h p : ℕ) : RangeP V0 K S u v (FarCoefficients V u) h 1 (p+1) :=
  (phys.far u).2.2 K kc hk h (p+1) m S v sc hs

include sc hs in
lemma F1_basis (p : ℕ) : ChargeP (p+1) ((heft q : ℝ) + (totalG v : ℝ))
    (fun (i : ↥S) t => lonelyG V0 (squeeze (-t) i.val) q v) :=
  Uniform.teeth_P phys.scope phys.dimensions sc hs phys.awake v q (p+1)

include kc hk in
lemma tariff_basis (k : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖coeff k (FarCoefficients V u x q)‖ ≤ C :=
  kc.exists_bound_of_continuousOn (((phys.far u).2.1 q k).mono hk)

include kc hk in
lemma tariff_charge (p : ℕ) : ChargeP (p+1) 0
    (fun (i: ↥K) _ => FarCoefficients V u i.val q) := by
  intro k _; obtain ⟨C,h⟩ := tariff_basis phys kc hk u q k
  exact Rain.cash ⟨C, fun i => h _ i.property⟩

include kc hk sc hs in
/-- Full, on unconverted arguments; formal OPE on this geometry handles every
horizon h so we can use whichever fixed one. -/
lemma Full_basis (h p : ℕ) : ChargeP (p+1) (totalG v : ℝ)
    (fun (i : ↥K × ↥S) t => party V0 i.1.val (squeeze (-t) i.2.val) u v) := by
  let L := fun (i : ↥K × ↥S) (t : ℝ) => Lamp V0 h (squeeze (-t) i.2.val) v
    (FarCoefficients V u i.1.val)
  have priced (q : Q G) := ChargeP.grow (F1_basis phys sc hs v q p)
    (show (totalG v:ℝ) ≤ (heft q:ℝ) + (totalG v:ℝ) by exact le_add_of_nonneg_left (by positivity))
  have pay : ChargeP (p+1) (totalG v:ℝ) L := by
    unfold L Lamp Settle
    apply ChargeP.sum; intro i _
    apply ChargeP.sum; intro j _
    exact ChargeP.times ((tariff_charge phys kc hk u (own j) p).pull Prod.fst)
      ((priced (own j)).pull Prod.snd)
  have res := ChargeP.plus (ChargeP.grow (FO_basis phys kc hk sc hs u v h p)
    (show (totalG v:ℝ) ≤ (h:ℝ)+1+(totalG v:ℝ) by exact le_add_of_nonneg_left (by positivity))) pay
  simpa only [Basket,L,sub_add_cancel] using res

include kc hk sc hs
lemma FO_spatial (h k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
    ∀ x ∈ K, ∀ y ∈ S,
      ‖coeff k (party V0 x (T • y) u v - Lamp V0 h (T • y) v (FarCoefficients V u x))‖ ≤
        C*(1+Real.log T)^a * (T^(h+1+totalG v))⁻¹ := by
  obtain ⟨C,hC,a,hw⟩ := toSpatial (h+1+totalG v)
    (by simp only [Nat.cast_add,Nat.cast_one]; exact FO_basis phys kc hk sc hs u v h k k (Nat.lt_succ_self _)
      : Rain (↑(h+1+totalG v) : ℝ) (fun (i : ↥K × ↥S) t =>
        coeff k (Basket V0 u v (FarCoefficients V u i.1.val) h i.1.val (squeeze (-t) i.2.val))))
  refine ⟨C,hC,a,?_⟩; filter_upwards [hw,eventually_gt_atTop (0:ℝ)] with T hw ht x hx y hy
  rw [← squeeze_log ht]; exact hw (⟨x,hx⟩, ⟨y,hy⟩)

lemma Full_spatial (h k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
    ∀ x ∈ K, ∀ y ∈ S, ‖coeff k (party V0 x (T • y) u v)‖ ≤
        C*(1+Real.log T)^a * (T^(totalG v))⁻¹ := by
  obtain ⟨C,hC,a,hw⟩ := toSpatial (totalG v) (Full_basis phys kc hk sc hs u v h k k (Nat.lt_succ_self _))
  refine ⟨C,hC,a,?_⟩; filter_upwards [hw,eventually_gt_atTop (0:ℝ)] with T hw ht x hx y hy
  rw [← squeeze_log ht]; exact hw (⟨x,hx⟩, ⟨y,hy⟩)

omit kc hk in
lemma F1_spatial (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
    ∀ y ∈ S, ‖coeff k (lonelyG V0 (T • y) q v)‖ ≤
        C*(1+Real.log T)^a * (T^(heft q + totalG v))⁻¹ := by
  obtain ⟨C,hC,a,hw⟩ := toSpatial (heft q+totalG v)
    (by rw [Nat.cast_add]; exact F1_basis phys sc hs v q k k (Nat.lt_succ_self _)
      : Rain (↑(heft q+totalG v):ℝ) (fun (i : ↥S) t =>
        coeff k (lonelyG V0 (squeeze (-t) i.val) q v)))
  refine ⟨C,hC,a,?_⟩; filter_upwards [hw,eventually_gt_atTop (0:ℝ)] with T hw ht y hy
  rw [← squeeze_log ht]; exact hw ⟨y,hy⟩

/-## Pay the running columns only after taking their homogeneous decay prices. -/
omit kc hk sc hs phys
variable (law : Law V ψ B)
include law

/-- Per basis tuple. Using the expansion in precisely those columns, the product of
occupied Far weights T^(totalG v) (`reflectV`, out front) cancels, including in the
remainder. No change of horizons or crop needed when taking arbitrary Far scale. -/
lemma cancel_powers {I : Type} (F : I → Points m → Scan G m → PowerSeries ℂ) {a : ℝ} (y : I → Points m)
    (pay : ∀ j : LivesP v, ChargeP (p+1) (a+(totalG v:ℝ))
      (fun i t => F i (squeeze (-t) (y i)) (decode v j))) :
    ChargeP (p+1) a (fun i t => LensT B t (F i) (y i) v) := by
  apply ChargeP.grow (a:=-(totalG v:ℝ)+(a+(totalG v:ℝ)))
  · apply ChargeP.joint reflectV
    exact cost_tag (Uniform.flips (rhythm_v law)) v _ pay
  · exact le_of_eq (by ring)

include phys kc hk sc hs
lemma loose_price (h p : ℕ) : ChargeP (p+1) ((h:ℝ)+1)
    (fun (i : ↥K × ↥S) t => looseT B V0 t u v (FarCoefficients V u) h i.1.val i.2.val) := by
  simp_rw [loose]; exact cancel_powers v law _ _
    (fun j => FO_basis phys kc hk sc hs u (decode v j) h p)

lemma show_price (h p : ℕ) : ChargeP (p+1) 0
    (fun (i : ↥K × ↥S) t => ShowT B V0 t i.1.val u i.2.val v) := by
  exact cancel_powers v law (fun (i : ↥K × ↥S) y w => party V0 i.1.val y u w) (fun i => i.2.val) (a:=0) (fun j => by
    rw [zero_add]; exact Full_basis phys kc hk sc hs u (decode v j) h p)

omit kc hk in
lemma long_price (p : ℕ) : ChargeP (p+1) (heft q : ℝ)
    (fun (i : ↥S) t => LongT B V0 t q i.val v) :=
  cancel_powers v law _ _ (fun j => F1_basis phys sc hs (decode v j) q p)
end YM.FVA2.GradedFar
