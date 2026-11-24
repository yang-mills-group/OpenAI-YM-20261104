import YM.AllOrder.Wheel.Wage
import YM.Comparison.RG02.Adjacent.Compatibility
import YM.Qlocal.Bless
/-!
Forward-reset arithmetic for model curvature terms with prefactor `g^e/g^k`, e an order, k
an (independent) curvature rank. This preserves the mark coordinates. Uses the formal reset
measurements supplied by the Floe Pace (`Coin` includes order-2 shift with no leading unit).
Conventions: direction "forward" means substitute *model* coarse coupling written in fine
coupling; hence `forward` is a series multiplier on a **post-reset** term to get its appearance
in **fine** units. Curvature arguments in this operation have NO change (they're actual
fields). `Adjacent.born/back/direct` on the perturbative representation have additional change of
log-link test fields `x` (these included the coupling!).

Identities, and a predicated symbolic cost theorem. Does not identify the prescription with the
running beta, nor estimate the analytic remainders. May instantiate with THAT Coin later. Notice
`raise` goes from pre-reset order up to any higher order and uses *the same rank*. No coefficients
constructed via numerical ratio presents as a perturbative answer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Finset
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open PositionX.Jet
open Comparison.RG02 Comparison.RG02.Adjacent
open scoped Topology BigOperators Classical ContDiff
variable (q : Coin) (q₀ : q 0 = 0) (r e k : ℕ)
/-- The Coin does NOT include the structural (unit) zeroth entry. -/
def calibration : Caliber := ⟨fun i => if i = 0 then 1 else q i, if_pos rfl⟩
local notation "D" => calibration q
include q₀
lemma tariff_eq (x : ℝ) : (D).tariff r x = 1 + PositionX.Jet.delay q r x := by
  have h (i : ℕ) : x ^ i * (D).measure i = (if i = 0 then 1 else 0) + x ^ i * q i := by
    by_cases he : i = 0 <;> simp [he, calibration, q₀]
  unfold Caliber.tariff PositionX.Jet.delay
  simp_rw [h]; rw [Finset.sum_add_distrib]; simp
lemma clock_eq (β : ℝ) : Wheel.now q r β = β * (D).tariff r (ConnectedActivityE6.Coat.gStep β) := by
  rw [tariff_eq q q₀]
set_option quotPrecheck false
local notation "B" => (calibration q).direct r
open Comparison.RG02.Moving.Path
/-- Ratio W(t) of a term of kinetic degree e and curvature rank k,
using the tariff offset f (β model map β ⟼ β*(1+f)). -/
def indexT (e k : ℕ) : ℝ := ((k:ℝ)-e)/2
/-- The multiplier on this term from substituting the formal coupling change, before pricing
  the winding (also correct on a term with given physical marks, if label names/sizes unchanged) -/
def forward (q : Coin) (e k : ℕ) : Word ℝ := Pace.ladder (indexT e k) q
lemma rating_eval (x : ℝ) (he : 0 ≤ 1 + PositionX.Jet.delay q r x) : (B).rating x=(1+PositionX.Jet.delay q r x)^(-(1/2:ℝ)):= by
  unfold Caliber.direct
  dsimp only [tariff_eq q q₀]
  rw [Real.rpow_neg he, Real.sqrt_eq_rpow, tariff_eq q q₀]
-- at actual-use epochs on real coupling, applies to the *estimated* positive price
omit q₀ in
lemma tags_rpow {x : ℝ} (hx : 0 < x) : tags 0 e k (x ^ (-(1/2:ℝ)))= x ^ (indexT e k) := by
  have v : ∀ (y:ℝ) (i:ℕ), (x^y)^i=x^(y*i):= fun y i => (Real.rpow_mul_natCast hx.le y i).symm
  rw [tags, zpow_zero, one_mul, inv_pow, v _ e, v _ k, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  unfold indexT; ring_nf
lemma acts : Act r (fun t => tags 0 e k ((B).rating t)) (forward q e k) := by
  let f := PositionX.Jet.delay q r
  have h : Act r (fun t => (1+f t)^(indexT e k)) (forward q e k) :=
    Pace.coin_word _ (Act.swell q le_rfl) q₀
  apply h.realizes
  filter_upwards [(D).rates r] with t ht
  rw [tariff_eq q q₀] at ht
  rw [rating_eval q q₀ _ _ ht.le, tags_rpow e k ht]
lemma motion_paid (i n K : ℕ) (hij : i ≥ n) (hj : i - n ≤ r) (he : e + K = n + k) :
    motion (Adjacent.money B 0 n K) i = Complex.ofReal (forward q e k (i - n)) := by
  rw [Adjacent.triangular, if_pos hij]
  have g : (fun t : ℝ => (tags 0 n K ((B).rating t):ℂ)) =ᶠ[𝓝 0]
    Complex.ofRealCLM ∘ fun t : ℝ => tags 0 e k ((B).rating t) :=
      ((B).bright).mono fun t ht => by
        change ↑(tags 0 n K ((B).rating t)) = (↑(tags 0 e k ((B).rating t)):ℂ)
        rw [exchange _ _ _ ht.ne', exchange _ _ _ ht.ne',
            show (0:ℤ)+(n:ℤ)-K=0+e-k by omega]
  rw [Moving.Shift.mgerm g]
  let f := Complex.ofRealCLM ∘ fun t : ℝ => tags 0 e k ((B).rating t)
  rw [← show someJ f (i-n)=motion f (i-n) from (by unfold motion someJ Comparison.RG02.Assembly.jet; rw [iteratedDeriv_eq_iteratedFDeriv])]
  exact ((acts q q₀ r e k).linear (L:= Complex.ofRealCLM)).writes (i-n) hj

-- Triangular model update. Coefficients applying to the identical curvature packet as it
-- becomes a term n orders higher. Presentations can retain all the paths/tests on that packet.
omit q₀
noncomputable def raise (q : Coin) (e k n : ℕ) : ℝ :=
  if n=0 then 1 else
    -(∑ j ∈ (Finset.range n).attach, raise q e k j.val * forward q (e+j.val) k (n-j.val))
termination_by n
decreasing_by exact Finset.mem_range.mp j.property
lemma raise_recurse (n : ℕ) (hn : n ≠ 0) : raise q e k n = -(∑ j∈range n, raise q e k j * forward q (e+j) k (n-j)):= by
  rw [raise, if_neg hn]
  exact congr_arg (-·) (Finset.sum_attach (f:=fun j=>raise q e k j * forward q (e+j) k (n-j)) _)
lemma raise_zero : raise q e k 0=1:= by rw [raise, if_pos rfl]
include q₀
/-- Convolving the generated new curvature order slots (raised to `e+j`) with the Taylor
 expansion of their forward unit multiplier gives precisely the one original order `e`. -/
lemma triangular (n : ℕ) : (∑ j∈range (n+1), raise q e k j * forward q (e+j) k (n-j)) = if n=0 then 1 else 0:= by
  split
  next he => subst n; simp [raise_zero, forward, Pace.start _ q₀]
  next he =>
    rw [Finset.sum_range_succ, Nat.sub_self, show forward q (e+n) k 0=1 from Pace.start _ q₀,
      mul_one, raise_recurse q e k n he]
    abel
lemma raised_from (i : ℕ) (hi : e ≤ i) :
    (∑ j∈Finset.Icc e i, raise q e k (j-e) * forward q j k (i-j)) = if i=e then 1 else 0:= by
  rw [← show ∑ j∈range (i-e+1), (raise q e k j * forward q (e+j) k (i-e-j))= ∑ j∈Icc e i, raise q e k (j-e) * forward q j k (i-j) from ?_, triangular q q₀]
  · simp only [show i-e=0 ↔ i=e from (by omega)]
  refine Finset.sum_bij (fun j _ => e+j) ?_ ?_ ?_ ?_
  · intro j hj; rw [Finset.mem_Icc]; simp only [mem_range] at hj; omega
  · intro j hj n hn hh; omega
  · intro j hj; have h:= Finset.mem_Icc.mp hj; refine ⟨j-e, mem_range.mpr (by omega), by omega⟩
  intro j hj; rw [Nat.add_sub_cancel_left, Nat.sub_add_eq]

omit q₀ -- now Estimate
variable {ι : Type} {μ : ι → ℝ} {p : ι → Coin} {m : ℕ}
open AllOrder.Ink
/-- Symbolic (teller/clock) cost. -/
lemma raises_cost (L : ℕ) (f : ∀ j ≤ L, Pace.Cost μ m (fun i=>p i j)) (n : ℕ) (h : n ≤ L) : Pace.Cost μ (m*n) (fun i => raise (p i) e k n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0:n=0
    · subst n; simp_rw [raise_zero]; exact Pace.Cost.fixed _
    simp_rw [raise_recurse _ e k n h0]
    refine Pace.Cost.neg (Pace.Cost.sum ?_)
    intro j hj; have hj:= Finset.mem_range.mp hj
    have hL : Pace.Cost μ (m*(n-j)) (fun i=>forward (p i) (e+j) k (n-j)) := Pace.Cost.transfer (k:=m) (fun v hv=> f v (by omega)) _
    have hn : m*n=m*j+m*(n-j):= by rw [← mul_add, show j+(n-j)=n by omega]
    exact hn.symm ▸ Pace.Cost.mul (ih j hj (hj.le.trans h)) hL
end YM.Qlocal.Moonset
