import YM.FVA2.O.Canon.Docket

/-!
# The unconverted prices to use at the Far positions (F.O & F.1)

`Physical` here is the *formal* array property of Canon/Docket. In the application it is
on `Measure.outlook` from Match. Use the estimates `O/Enh` of the original project, as in
`YM/WiderProfiles/Basket.lean:separate_predictor_inputs`. `s` here is log T (NOT coupling).
Families over K × S subtypes: uniform! Constants can depend on any of the fixed configuration
and order parameters, but not e.g. on positions within the sets or T. Include also the derived
FULL size price (F after F.O), retaining the homogeneous power. These are on basis labels
of all engineering grades (not a norm-price on a single horizon).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Rake MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Bind O.Canon
variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m : ℕ} {K : Set (Points n)} {S : Set (Points m)}
section Demand
variable (H : O.Canon.Physical V R B) (u : Scan G n) (v : Scan G m)
    (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
local notation "Ω" => install V
local notation "cf" => FarCoefficients V
include H

include hK hc hS hy in
lemma FO (d h : ℕ) :
    ChargeP d ((h : ℝ)+1+(totalG v : ℝ)) (fun (i : ↥K × ↥S) s =>
      Basket Ω u v (cf u i.1.val) h i.1.val (squeeze (-s) i.2.val)) :=
  (H.far u).2.2 _ hK hc h d m S v hS hy

include hS hy in
lemma F1 (q : Q G) (d : ℕ) :
    ChargeP d ((heft q : ℝ)+(totalG v : ℝ)) (fun (i : ↥S) s =>
      lonelyG Ω (squeeze (-s) i.val) q v) :=
  O.Enh.Uniform.teeth_P H.scope H.dimensions hS hy H.awake v q d

include hK hc
/-- Need a compact-x price on *the actual* continuum coefficients `FarCoefficients`. -/
lemma Fcompact (q : Q G) (j : ℕ) :
    ∃ M : ℝ, ∀ x ∈ K, ‖coeff j (FarCoefficients V u x q)‖ ≤ M :=
  hK.exists_bound_of_continuousOn (((H.far u).2.1 q j).mono hc)

lemma Fcoeff (q : Q G) (d : ℕ) :
    ChargeP d 0 (fun (i : ↥K) (_ : ℝ) => cf u i.val q) := by
  intro j _
  obtain ⟨M,h⟩ := Fcompact H u hK hc q j
  exact Rain.cash ⟨M,fun i => h i.val i.property⟩

include hS hy
/-- F.1 and the compact coefficient price pay even the full moment price, with the Far
grading power intact. (F.O has the additional decay.) -/
lemma Ffull (d h : ℕ) :
    ChargeP d (totalG v : ℝ) (fun (i : ↥K × ↥S) s =>
      party Ω i.1.val (squeeze (-s) i.2.val) u v) := by
  let c := cf u
  have form (x : Points n) (y : Points m) :
      party Ω x y u v = Basket Ω u v (c x) h x y +
        ∑ q : Dframe.Toon G h, c x (Dframe.flash q) * lonelyG Ω y (Dframe.flash q) v := by
    rw [O.Read.Fare, Basket, sub_add_cancel]
  simp_rw [form]
  refine ChargeP.plus ((FO H u v hK hc hS hy d h).grow (by linarith [Nat.cast_nonneg (α:=ℝ) h])) ?_
  refine ChargeP.sum _ fun j (_ : j ∈ (Finset.univ : Finset (Dframe.Toon G h))) => ?_
  exact ChargeP.times ((Fcoeff H u hK hc (Dframe.flash j) d).pull Prod.fst)
    (((F1 H v hS hy (Dframe.flash j) d).pull Prod.snd).grow (by linarith [Nat.cast_nonneg (α:=ℝ) (heft (Dframe.flash j))]))
end Demand

/-- Read any of these prices, at integral exponent, in T coordinates. -/
lemma post_eq_nat (w k : ℕ) (T : ℝ) (hT : 0 < T) :
    post (w : ℝ) (Real.log T) k = (T⁻¹)^w*(1+Real.log T)^k := by
  unfold post
  rw [mul_comm (-(w:ℝ)), Real.exp_mul, Real.exp_log hT, Real.rpow_neg hT.le,
    Real.rpow_natCast, inv_pow, mul_comm]

lemma squeeze_T (T : ℝ) (hT : 0 < T) (y : Points m) : squeeze (-Real.log T) y = T • y := by
  rw [squeeze, neg_neg, Real.exp_log hT]

section Money
variable {I : Type} (a : ℝ) (g : I → ℝ → ℂ) {w : ℕ}

lemma rain_price_T {F : I → ℝ → ℂ} (H : Rain (w : ℝ) F) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ᶠ T : ℝ in atTop,
      ∀ i, ‖F i (Real.log T)‖ ≤ C * (T⁻¹)^w * (1+Real.log T)^k := by
  obtain ⟨C,hC,k,h⟩ := H
  refine ⟨C,hC,k,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually h, eventually_gt_atTop (0:ℝ)] with T h ht
  intro i
  rw [mul_assoc, ← post_eq_nat w k T ht]
  exact h i
end Money
end YM.FVA2.GradedFar259
