import YM.RG12.Canonical.Ticket
import YM.RG12.Frames.Tests
import YM.RG12.Frames.Rest

/-!
# Actual matrix bridge from comparable scale readings on independent physical bases

In addition to successive near-free tests, require comparisons at the comparable measuring
age `age k` on columns from the canonical limit charts. Test upper on ALL these columns (as
needed to cover the outlet); lower on a selected INDEPENDENT set of pivots with known
representatives, which may differ from that age's measuring pivots, e.g. all these new ones
can use the same horizon d. No filtration assumption on the new pivots; the moving frames do
need filtration compatibility at every scale. Costs on these canonical-limit comparisons can
already incur log budgets in the geometry. NO coupling or scale law identification in here:
as well as the quantitative adj testing over *all* late ages those remain producer goals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Finset Lattice RG Source Frames
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {hC : C.Makes} {φ : Filter UVIndex} [φ.NeBot]
  {M : ∀ d : ℕ, ℕ → RepChart C d} {S : Table C.book} {B : DiffPlan S}
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable {s t u : ℕ → ℝ} {Y : ℕ → Col V →ₗ[ℂ] S.Field d} {P : Col V ≃ₗ[ℂ] S.Field d}
  {J : ℕ → Col V ≃ₗ[ℂ] Col V} {R : ℕ → S.Field d → ℝ} {K : ℝ} {p b n₀ : ℕ}
  [FiniteDimensional ℂ (Col V)]

/-- This exact engineering belongs here and not in `RepChart` (to keep
`quota_atK` exact without factors). -/
def engineering (M : ∀ d, ℕ → RepChart C d) (d k : ℕ) : C.label d →ₗ[ℂ] S.Field d :=
  (((C.S.a k)^d:ℝ):ℂ) • (S.project d).comp (M d k).toLinearMap

lemma engineering_at {x : C.label d} {k : ℕ} :
    engineering (S:=S) M d k x = (((C.S.a k)^d:ℝ):ℂ) • S.project d (M d k x) := rfl

/-- A log age used for adjacent scale readings charges the (unique) physical calendar on C.
Require only that the canonical k-readout can use some scale along it practically affordable
at k. Finite onset stages and constants can depend on d through all of this. -/
structure Stop (C : Family G) (s t : ℕ → ℝ) (n : ℕ) (m : ℕ → ℕ) (k e : ℕ) where
  approaches : n ≤ m k
  clock : s (m k) ≤ C.path.levels.clock.hatBeta k ^ e
  match_length : t (m k) ≤ C.S.a k * C.path.levels.clock.hatBeta k ^ e ∧
    C.S.a k ≤ t (m k) * C.path.levels.clock.hatBeta k ^ e

/-- A separate *uncalibrated* comparison on the actual normalized k columns of horizon d.
R in both lines must still be on the same **fixed physical space**, here we are just evaluating
it on normalized canonical columns rather than the march's preferred fields. -/
structure ReadingAt (C : Family G) (S : Table C.book) (d : ℕ) (V : Grade d → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
    (R : S.Field d → ℝ) (k : ℕ)
    (M : ∀ d : ℕ, ℕ → RepChart C d) (Z : Col V →ₗ[ℂ] C.label d) (e : ℕ) where
  look (x : C.label d) : R (engineering (S:=S) M d k x) ≤ C.path.levels.clock.hatBeta k ^ e * mass C d x
  norm (x : Col V) : mass C d (Z x) ≤ C.path.levels.clock.hatBeta k ^ e * ‖x‖
  price (x : Col V) : ‖x‖ ≤ C.path.levels.clock.hatBeta k ^ e * R (engineering (S:=S) M d k (Z x))

-- structure with only Prop fields is Type by default; make predicates for ∀ᶠ
variable (H : Consecutive s t u Y P R J K p b n₀)
variable (m : ℕ → ℕ) {e : ℕ} (hS : ∀ᶠ k in atTop, Nonempty (Stop C s t n₀ m k e))
    (Z : ℕ → Col V →ₗ[ℂ] C.label d)
    (hM : ∀ᶠ k in atTop, Nonempty (ReadingAt C S d V (R (m k)) k M (Z k) e))
    (hG : G.Simple)

include H hS hM hG
lemma march_right : RightPrice C S M d := by
  obtain ⟨U,hU,A,ha⟩:= Frames.enough H
  let a:= C.S.a; let r:= transportPower d p (p+b+4)
  intro x; let L:ℝ:= K * coins (p+b+4) (compress (R n₀ ∘ Y n₀)) (s n₀) ((U n₀).symm x) * t n₀ ^ d
  have hh:= H.charges n₀ le_rfl; have hk:= hh.legal
  have ht : 1 ≤ s n₀:= hk.trans (H.times _ le_rfl).1
  have hf : 0 ≤ L := mul_nonneg (mul_nonneg (zero_le_one.trans hk)
    (coins_nonneg (fits_compress hh) (zero_le_one.trans ht) _)) (pow_nonneg (H.spacing _ le_rfl).1.le _)
  refine ⟨e+e+1+e*d+e*r,?_⟩
  filter_upwards [hS,hM,(hat_grows (C:=C) hG).eventually_ge_atTop 1,
    (hat_grows (C:=C) hG).eventually_ge_atTop (K*L)] with k ⟨hE⟩ ⟨hB⟩ hv hv'
  let y:=C.path.levels.clock.hatBeta k; let n:=m k; let z:= Z k
  let X:=engineering (S:=S) M d k; have hb:=hE.approaches
  let T:=R n; let W:= U n
  have hc: 0 ≤ y ^ e := pow_nonneg (zero_le_one.trans hv) _
  have hz:T 0=0:= by simpa [Function.comp] using (H.charges _ hb).zero
  have hi : Injective (X.comp z):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro v ht
    have hq:= hB.price v; change _ ≤ y^e * T ((X.comp z) v) at hq
    rw [ht,hz,mul_zero] at hq; exact norm_le_zero_iff.mp hq))
  have hi' : Surjective ((P.symm.toLinearMap.comp X).comp z):= LinearMap.injective_iff_surjective.mp (P.symm.injective.comp hi)
  obtain ⟨v,hvZ⟩:= hi' (P.symm x)
  have hw : X (z v)=x:=P.symm.injective hvZ; let c:=(↑(a k ^ d):ℂ)
  refine ⟨c • z v,?_,?_⟩
  · rw [map_smul,map_smul]; exact hw
  have hY := col_ticket ha (Fin.last d) x (by intro j hj; exact False.elim (by have := j.is_le; have h : d < j.val:=hj; omega)) n hb
  change ‖W.symm x‖ ≤ _ * _ * _^r at hY
  have hg : t n > 0:= (H.spacing _ hb).1; let w:= W.symm x
  have hy : ‖w‖ ≤ L * ((t n)^d)⁻¹ * s n^r := by
    refine hY.trans_eq ?_; change _*(t n₀/t n)^d*s n^r= _; unfold L; rw [div_pow]; ring_nf
    try rfl
  have he' : T x ≤ K * ‖w‖:=by
    have heS:= (H.charges n hb).upper w; dsimp only [Function.comp_apply] at heS; rw [← hU n hb] at heS; exact W.apply_symm_apply x ▸ heS -- motive?
  have hN := hB.price v; change _ ≤ _ * T (X (z v)) at hN; rw [hw] at hN
  have hZ : mass C d (z v) ≤ y^e * (y^e * (K*(L * ((t n)^d)⁻¹ * s n^r))) := (hB.norm v).trans
    (mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_left (he'.trans (mul_le_mul_of_nonneg_left hy (zero_le_one.trans hk))) hc)) hc)
  have he : a k^d * ((t n)^d)⁻¹ ≤ y^(e*d):= by
    rw [pow_mul, ← div_eq_mul_inv,div_le_iff₀ (pow_pos hg d),mul_comm, ← mul_pow]
    exact pow_le_pow_left₀ (C.S.a_pos k).le hE.match_length.2 d
  have hi : 0 ≤ s n:= zero_le_one.trans (hk.trans (H.times _ hb).1)
  have hm : mass C d (c • z v)= (a k)^d * mass C d (z v):=by
    change (C.labels.level d).coeffSize _= _; unfold Labels.Frame.coeffSize mass c; simp_rw [Pi.smul_apply,norm_smul,Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (show 0<a k from C.S.a_pos k).le d)]
    exact (mul_sum ..).symm
  calc
    _ = _ := hm
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (pow_nonneg (C.S.a_pos k).le _)
    _ = y^(e+e)*(K*L)*(a k^d*((t n)^d)⁻¹)*s n^r:=by rw [pow_add]; ring
    _ ≤ y^(e+e)*y*y^(e*d)* (y^e)^r:= by
      have hx : 0 ≤ a k^d*((t n)^d)⁻¹:= mul_nonneg (pow_nonneg (C.S.a_pos k).le _) (inv_nonneg.mpr (pow_nonneg hg.le _)); have hy:0 ≤ y:=zero_le_one.trans hv
      gcongr
      exact hE.clock
    _ = y^(e+e+1+e*d+e*r):=by simp only [pow_add,pow_one,pow_mul]

-- all rows at fixed d; P must implement the exact rise filtration
lemma march_row (w : ℕ) (hP : ∀ i : Grade d, i.val < w → ∀ v : V i,
    P (put V i v) ∈ LinearMap.range (B.rise i.is_le)) : RowPrice C S B M d w := by
  intro D hw hD
  let G': Grade d:= ⟨w,Nat.lt_succ_of_le hw⟩
  have hl:∀x ∈prev V G', D (P x)=0:=by
    intro x hx
    rw [← by_grade V x, map_sum,map_sum]; apply Finset.sum_eq_zero
    intro i _
    rcases le_or_gt G' i with he|he
    · rw [hx i he]; simp [put]
    have hr:i.val<w:= he
    obtain ⟨v,hv⟩:= hP i hr (x i); rw [← hv]; exact hD i.val hr v
  obtain ⟨U,hU,A,ha⟩:= Frames.enough H
  let r:= transportPower d p (p+b+4)
  let L:ℝ:= (((d+1:ℕ):ℝ)*K^2*startNorm U D n₀) * ((t n₀)^w)⁻¹; have hh:= H.charges n₀ le_rfl; have hk:= hh.legal
  have ht:0≤ startNorm U D n₀:=norm_nonneg _; have hf := (H.spacing _ le_rfl).1
  have hL:0≤L:=by unfold L; positivity
  refine ⟨1+e*w+e*r+e,?_⟩
  let y:= C.path.levels.clock.hatBeta
  filter_upwards [hS,hM,(hat_grows (C:=C) hG).eventually_ge_atTop (L*K), (hat_grows (C:=C) hG).eventually_ge_atTop 1] with k ⟨hE⟩ ⟨hB⟩ hLK hq x
  let n:=m k; let a:=C.S.a; let X:= engineering (S:=S) M d k
  have hN:= hE.approaches; have hp := H.charges _ hN; let P':= U n
  let v:= P'.symm (X x)
  have hu: Y n v=X x:= by rw [← hU n hN]; exact P'.apply_symm_apply _
  have hS:0 ≤ s n:= zero_le_one.trans (hk.trans (H.times _ hN).1)
  have hX : ‖v‖ ≤ K * ((y k)^e * mass C d x):= by
    have hv:= hp.lower v; dsimp only [Function.comp_apply] at hv; rw [hu] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left (hB.look x) (zero_le_one.trans hk))
  have hc : 0 ≤ y k ^ e := pow_nonneg (zero_le_one.trans hq) _; have hc':0≤y k:=zero_le_one.trans hq
  have hR := row_ticket ha D hl n hN v; change ‖D (P' v)‖ ≤ _*(t n/t n₀)^w*(s n)^r*_ at hR
  rw [P'.apply_symm_apply] at hR -- v let
  have hr':0<t n:= (H.spacing n hN).1
  have hr : ‖D (X x)‖≤ ((y k)^(1+e*w+e*r+e)*mass C d x)*a k^w := by
    apply hR.trans
    have he: 0 ≤ a k:= (C.S.a_pos k).le; have hz:= mass_nonneg C d x
    calc
      _ = L*(t n)^w*(s n)^r*‖v‖:=by rw [div_pow]; unfold L; ring
      _ ≤ L*((a k*(y k)^e)^w)*((y k)^e)^r*(K*((y k)^e*mass C d x)):=by
        gcongr
        · exact hE.match_length.1
        exact hE.clock
      _ = ((L*K)*((y k)^(e*w+e*r+e)* mass C d x))*a k^w:=by rw [mul_pow,pow_add,pow_add,pow_mul,pow_mul]; ring
      _ ≤ _:= by rw [show 1+e*w+e*r+e=1+(e*w+e*r+e) by omega,pow_add (y k) 1,pow_one, mul_assoc (y k)]; gcongr
  have he:= C.S.a_pos k
  let k' := 1+e*w+e*r+e
  rw [engineering_at,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg he.le d)] at hr -- X let
  have ha : (a k)^d=(a k)^w*(a k)^(d-w):= by rw [← pow_add]; congr 1; omega
  rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos he _)]; apply le_of_mul_le_mul_left _ (pow_pos he w)
  change (C.S.a k)^w*_ ≤ _
  convert hr using 1
  · change _= a k^d*_ ; rw [ha,mul_assoc]; ring
  ring
end YM.RG12
