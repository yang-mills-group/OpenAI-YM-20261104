import YM.RG02.Marker.Series

/-!
# Finite cuts and screens

Through-order truncations and adding exclusions or keeping only a subsystem
of source names. Does not authorize equating two unmasked/masked arrays; use
on the same polynomial. Also arbitrary algebraic frame/dimension unit changes
that are marker algebra maps and respect the augmentation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Grade
open Finset Marker Extra.Trajectories Marks PowerSeries
open scoped BigOperators
variable {ι J : Type} [DecidableEq ι] [DecidableEq J] {R : Census ι} {S : Census J}

/-- Through the *inclusive* upper grade. -/
def Through (n : ℕ) (x y : Script R) := ∀ i, i≤n → coeff i x=coeff i y
lemma through_iff {x y : Script R} {r : ℕ} : Through r x y ↔ encode r x=encode r y := encode_same.symm

-- For calculus a bare assertion of equality under integration does
-- not permit using these lemmas on the analytic representation.
namespace Through
variable {r : ℕ} {x y z w : Script R}
lemma mul (h : Through r x y) (h' : Through r z w) : Through r (x*z) (y*w) :=
  through_iff.mpr (by rw [encode_mul,encode_mul,through_iff.mp h,through_iff.mp h'])
lemma point (h : Through r x y) : basepoint x=basepoint y := by rw [basepoint_read,basepoint_read,h 0 (Nat.zero_le _)]
lemma scalarPart (h : Through r x y) : Through r (scalar R (den x)) (scalar R (den y)) := by
  intro i hi; simp only [scalar,den,coeff_map,h i hi]
lemma ratio (h : Through r x y) (hX : basepoint x ≠ 0) : Through r (quotient x) (quotient y) := by
  have hk : basepoint y ≠ 0 := by rw [← h.point]; exact hX
  apply through_iff.mpr
  let c := encode r (scalar R (den x))
  have hh : c=encode r (scalar R (den y)) := through_iff.mp h.scalarPart
  have hu : IsUnit c := by
    let p := encode r (scalar R (den x)⁻¹)
    have t : c*p=1 := by rw [show c*p = _ from (encode_mul ..).symm,
      ← map_mul,PowerSeries.mul_inv_cancel _ (by rwa [hasDen]),map_one,encode_one]
    exact ⟨⟨c,p,t,(mul_comm ..).trans t⟩,rfl⟩
  apply hu.mul_right_inj.mp
  calc
    _ = encode r x := by unfold c; rw [← encode_mul,unnormalized hX]
    _ = encode r y := through_iff.mp h
    _ = c * encode r (quotient y) := by rw [hh, ← encode_mul,unnormalized hk]
variable [Fintype ι]
lemma exponent (h : Through r x y) (hX : basepoint x=0) : Through r (exponential x) (exponential y) := by
  apply through_iff.mpr; rw [encode_exponential hX,encode_exponential (h.point.symm.trans hX),through_iff.mp h]
lemma toLog (h : Through r x y) (hX : basepoint x=1) : Through r (logarithm x) (logarithm y) := by
  apply through_iff.mpr; rw [encode_logarithm hX,encode_logarithm (h.point.symm.trans hX),through_iff.mp h]
end Through

-- Also use more general `renormalizing` maps below (e.g. dimensions).

section Map
variable (f : Poly R →ₐ[ℂ] Poly S)

local notation "L" => PowerSeries.map f.toRingHom

lemma respects_scalar (x : PowerSeries ℂ) : L (scalar R x)=scalar S x := by
  ext i j
  rw [scalar, scalar,coeff_map,coeff_map,coeff_map]
  change (f (Poly.bead R _)).part j = _
  rw [show f (Poly.bead R _)=Poly.bead S (coeff i x) from f.commutes _]

variable (hf : ∀ x, blank _ (f x)=blank _ x)
include hf

lemma respects_den (x : Script R) : den (L x)=den x := PowerSeries.ext fun i => by
  rw [den,den,coeff_map,coeff_map,coeff_map]; exact hf _

lemma respects_basepoint (x : Script R) : basepoint (L x)=basepoint x := by rw [← hasDen,respects_den f hf,hasDen]

lemma respects_quotient (x : Script R) : L (quotient x)=quotient (L x) := by
  unfold quotient; rw [respects_den f hf,map_mul,respects_scalar]

variable [Fintype ι] [Fintype J]

theorem respects_exp (x : Script R) (hx : basepoint x=0) : L (exponential x)=exponential (L x) := by
  apply PowerSeries.ext; intro i
  let k := i + max (Fintype.card ι) (Fintype.card J) + 1
  rw [coeff_map, exponential_terms hx _ k (by dsimp [k]; omega),exponential_terms ((respects_basepoint f hf x).trans hx) i k (by dsimp [k]; omega)]
  rw [map_sum,map_sum,map_sum]; refine sum_congr rfl fun j _ => ?_
  rw [coeff_smul,coeff_smul, ← map_pow,coeff_map]
  exact map_smul f _ _

theorem respects_log (x : Script R) (hx : basepoint x=1) : L (logarithm x)=logarithm (L x) := by
  let y := logarithm x
  have he : basepoint (L y)=0 := (respects_basepoint f hf _).trans (base_logarithm hx)
  change L y = _
  rw [← exp_log hx, respects_exp f hf _ (base_logarithm hx),log_exp he]
end Map

/-- `Names` (adding exclusions and/or dropping some markers) is a concrete
map for this API, on the *same* Euler-coupled series. -/
def restrict (f : Names S R) : Poly R →ₐ[ℂ] Poly S where
  __ := f.restriction
  commutes' r := by
    change f.restriction (Poly.bead R r)= Poly.bead S r
    have h (c : Census J) : Poly.bead c r = r • (1 : Poly c) := Algebra.algebraMap_eq_smul_one r
    rw [show Poly.bead R r=r • (1:Poly R) from Algebra.algebraMap_eq_smul_one r,h, f.smul,map_one]

lemma restrict_part (f : Names S R) (x : Poly R) (s : S.Mode) :
    (Grade.restrict f x).part s=x.part (f.share s) := rfl
lemma restrict_blank (f : Names S R) (x : Poly R) : blank _ (Grade.restrict f x) = blank _ x := by
  change (Grade.restrict f x).part _=x.part _; rw [restrict_part,f.quiet]
lemma pointed (f : Names S R) (x : Poly R) (i : J) : Grade.restrict f (euler (f.e i) x) =
    euler i (Grade.restrict f x) := by
  ext s
  rw [restrict_part,part_euler,part_euler,restrict_part]
  by_cases h : i∈s.val
  · simp only [if_pos h, if_pos (show f.e i∈(f.share s).val from mem_image_of_mem _ h)]
  rw [if_neg h, if_neg (fun H => h ?_)]
  obtain ⟨k,hk,he⟩ := mem_image.mp H; exact (f.e.injective he) ▸ hk

lemma restrict_coeff (x : Script R) (f : Names S R) (k : ℕ) (s : S.Mode) :
    (coeff k (PowerSeries.map f.restriction x)).part s=(coeff k x).part (f.share s) := by
  rw [coeff_map]; rfl

end YM.RG02.Grade
