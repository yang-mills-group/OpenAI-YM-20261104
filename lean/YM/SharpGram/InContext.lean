import YM.SharpGram.Weak.Access
import YM.SharpGram.Common

/-!
# The all-k price obtained on the physical fields, independent of any perturbative matching

The remaining issue before MatrixTicket is the comparison of the fixed frames
to the measuring frames (or additional sharp estimates achieving the same
on the quotient). Make this precise below, and record the **unconditional**
result for all fields so far. The normalization in the measurement is the one
used on the exact quotient. The compatible basis has unit, H actions, and all
rise maps respected, within any fixed announced horizon, at the **same
spatial scale** therein, and is realized by actual all-cutoff matrix bounds
on both sides. There is no estimate here restricted to just a sequence of
capture k or any assumption about a limit after *rescaling those quotas*.
`X.radius` used for weak Gram tests (inspect `X.onLevel` for how far it can
be; may charge further polynomial powers of P). Exact engineering weights
exposed throughout.

This uses no successor estimates for relative **physical** frame orientation;
so the results are independent of new comparison machinery. For using such
orientation bounds later, our access implications use the actual tilted test
form and the named frames. The additional price in `FixedPrice` is deliberately
not requested on bare/off-shell labels at distance scale. Tests only through
any one X, and only in the true field quotients of this Final. No artifact of
representation or sublimit choice can be identified with a fixed reference sign
without that price. This price (or alternate bridge to the sharp bounds) is an
OPEN estimate, not simply a routine precision-slack reallocation! Need a new
physical estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Filter Set Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Further.CorrectedLift Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open OPE OPE.Log Weak Weak.Portfolio
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)} (X : Weak.Portfolio C U.room.cutoff D u)
local notation "F" => Cells.standard C
local notation "σ" => U.room.kernel.spin
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "V" => U.sector.derivatives
local notation "P" => C.path.levels.clock.hatBeta
local notation "a" => C.S.a

-- Additional cost -- true physical only
structure BasisMeter (Y : ℕ → ∀ d : ℕ, YM.Spin.change S d) : Prop where
  graded : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V (Maxwell.Free.scheme C.labels) σ θ (Y k) D
  price (d : Fin (D+1)) : ∃ δ K : ℝ, 0 < δ ∧ 0≤ K ∧
    ∀ᶠ k : ℕ in atTop, ‖inBasis U X k d (Y k d)‖ ≤ K ∧ coercive (inBasis U X k d (Y k d)) δ

-- Frame cost on fixed fields. One function price log at a time.
structure FixedPrice (Y : ℕ → ∀ d : ℕ, YM.Spin.change S d) : Prop extends BasisMeter U X Y where
  pullField (d : Fin (D+1)) (x : S.Field d) :
    ∃ p : ℕ, ∀ᶠ k in atTop, ‖(Y k d).symm x‖ ≤ P k^p / a k ^ d.val
  pushField (d : Fin (D+1)) (w : ℕ) (L : S.Field d →ₗ[ℂ] ℂ) (hw : w ≤ d.val) :
    Kills (C:=C) V hw L →
      ∃ p : ℕ, ∀ᶠ k in atTop, ∀ x, ‖L (Y k d x)‖ ≤ P k^p * a k^w * ‖x‖

structure PricedIn (Y : ℕ → ∀ d : ℕ, YM.Spin.change S d) : Prop extends BasisMeter U X Y where
  sources (d : Fin (D+1)) : ∃ p : ℕ, ∀ᶠ k : ℕ in atTop, ∀ x : S.Field d,
     ∃ (y : C.label d) (q : ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
       ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ P k^p * a k ^ d.val * ‖(Y k d).symm x‖
  reads (d : Fin (D+1)) : ∃ K : ℝ, 0 ≤ K ∧
     ∀ᶠ k in atTop, ∀ (v : Filter (ℕ×ℕ)) [v.NeBot], v ≤ u →
          ∀ (q : ℕ×ℕ → C.label d)(x : C.label d)(z:ℝ),
            (∀ᶠ i in v, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q v (𝓝 x) →
              ‖(Y k d).symm (S.project d x)‖ ≤ K / a k ^ d.val * z

variable (T : Facilities C f S)
variable {Y : ℕ → ∀ d : ℕ, YM.Spin.change S d}

/-- operator-norm residual estimate (not circular) via exact tilted detector. -/
lemma basisTest (h : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V (Maxwell.Free.scheme C.labels) σ θ (Y k) D)
    (he : ∀ d : Fin (D+1), Tendsto (fun k => inBasis U X k d (Y k d)) atTop (𝓝 (Portfolio.model C d))) :
    BasisMeter U X Y := by
  refine ⟨h,fun d => ?_⟩; obtain ⟨δ, hp, hT⟩ := Portfolio.freely (C:=C) d
  let K := Portfolio.model C d
  refine ⟨δ/2, δ/2+‖K‖, half_pos hp, by positivity, ?_⟩
  filter_upwards [SharpGram.stayNear (he d) (half_pos hp)] with k hk
  exact ⟨Portfolio.normBy hk,absorb K _ δ (δ/2) hT (by simpa only [sub_half] using hk)⟩

variable [u.NeBot] (hf : u ≤ f.fuse)
include hf T
lemma access (hB : BasisMeter U X Y) : PricedIn U X Y := by
  obtain ⟨w,r,D',hT⟩:=T.costlier
  have ht := hT.toTableTickets
  refine ⟨hB,fun d=>?_,fun d=>?_⟩
  · obtain ⟨δ,K,H,hK,H'⟩:= hB.price d
    obtain ⟨p,hp⟩ := Portfolio.entryUse U X ht hf T.simpleGate d K hK
    exact ⟨p,(hp.and H').mono fun i hi => hi.1 (Y i d) hi.2.1⟩
  obtain ⟨δ,K,H,hK,H'⟩:= hB.price d
  have hP := Portfolio.departUse U X ht hf T.simpleGate d δ H
  exact ⟨_, mul_nonneg (Real.sqrt_nonneg _) zero_le_two, (hP.and H').mono fun i hi => hi.1 (Y i d) hi.2.2⟩

lemma attains : ∃ Y : ℕ → ∀ d : ℕ, YM.Spin.change S d,
    PricedIn U X Y ∧
    ∀ d : Fin (D+1), Tendsto (fun k => inBasis U X k d (Y k d)) atTop (𝓝 (Portfolio.model C d)) := by
  obtain ⟨w,r,L,H'⟩:=T.costlier
  obtain ⟨p,hp,hA⟩ := X.tune_grades U H'.toTableTickets hf T.simpleGate
  have h d := aligned U X H'.toTableTickets hf T.simpleGate d (he:=hA d)
  exact ⟨p,access U X T hf (basisTest U X hp h),h⟩

include u
lemma access_inlet (hB : FixedPrice U X Y) (d : Fin (D+1)) (x : S.Field d) : Supplies C u d x := by
  obtain ⟨p,hp⟩:=(access U X T hf hB.toBasisMeter).sources d
  obtain ⟨r, hr⟩:= hB.pullField d x; refine ⟨p+r,?_⟩
  filter_upwards [hp,hr] with k hk hv; obtain ⟨y,q,h,hQ,he⟩:= hk x
  have hP := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have ha := C.S.a_pos k
  refine ⟨y,q,h,hQ,he.mono fun i hi=> hi.trans ?_⟩
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (mul_nonneg (pow_pos hP p|>.le) (pow_pos ha d.val|>.le))
    _ = _ := by rw [pow_add]; field_simp
lemma access_outlet (hB : FixedPrice U X Y) (d : Fin (D+1)) (w : ℕ) (L : S.Field d →ₗ[ℂ] ℂ) (hw : w ≤ d.val)
    (hL : Kills (C:=C) V hw L) : Releases C u d w L := by
  obtain ⟨K,hK,h⟩:=(access U X T hf hB.toBasisMeter).reads d
  obtain ⟨p,hp⟩:= hB.pushField d w L hw hL
  refine ⟨p+1,?_⟩; filter_upwards [hp,h,(hat_rate _ T.simpleGate).eventually_ge_atTop K] with k he hi hh v hv hV q x z hz hT
  have h0 : 0 ≤ z := by obtain ⟨l,hℓ⟩:= hz.exists; exact (quota_nonneg ..).trans hℓ
  have ht := he ((Y k d).symm (S.project d x)); rw [LinearEquiv.apply_symm_apply] at ht
  have hp := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have ha := C.S.a_pos k
  calc
    _ ≤ _ := ht
    _ ≤ (P k)^p * a k^w * _ := mul_le_mul_of_nonneg_left (hi v hV q x z hz hT) (mul_nonneg (pow_pos hp p).le (pow_pos ha w).le)
    _ = (P k)^p * K / a k^(d.val-w) * z := by
      rw [show a k ^ d.val=a k ^ (d.val-w)*a k^w from by rw [← pow_add, Nat.sub_add_cancel hw]]
      field_simp
    _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_right
                    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (pow_pos hp p|>.le))
                      (pow_pos ha _|>.le)) h0

end YM.SharpGram
