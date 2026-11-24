import YM.Planned.PRIMARY_INTEGRAL_295.Stain
import YM.RG12.Canonical.FromFrames
import YM.MergeProof.East.Ladle
/-!
# Alignment of the rank/readout receipt `Tested` to the MatrixTicket charts

At a station k, these readings actually span the engineering-scaled full columns, with log
costs *local at k* stemming from coupling conventions. This lets us estimate readings even on
null canonical axes from the rank theorem. Does NOT compare their limiting IR prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Set Filter Finset Lattice RG Source Next.Rank.Price
open Work.G08 Next.Rank.East
open scoped Topology BigOperators
variable {G:Gauge} {C:Family G} {d N p k:ℕ} (hC:C.Makes)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "F"=> C.labels.level d
variable (hr:C.ref d≤k)(hn:k≤N)
-- chart coordinates of the engineering-normalized station pivot, on the *same* k capture,
-- at each admitted cutoff, before any canonical chart observation limits.
def localFit (hC:C.Makes) (k N p:ℕ) (T:Module.End ℂ (C.label d)) (b:ℝ) : Module.End ℂ (C.label d) :=
  ((↑(C.S.a k ^ d : ℝ):ℂ)⁻¹) • ((charts C hC d k (N,p)).toLinearMap.comp (ladd C b k N p d T))
include hr hn
variable {T:Module.End ℂ (C.label d)} (h:Tested C d k N p T) (b:ℝ)

lemma local_awake (v:C.label d) : localFit hC k N p T b v = awake C d k N p (ladd C b k N p d T v):=by
  unfold localFit awake charts; rw [dif_pos ⟨hr,hn⟩,Complex.ofReal_pow]; rfl

omit hr hn in
lemma atK_local (v:C.label d) :
    ((↑(C.S.a k ^ d : ℝ):ℂ)) • atK C hC d k (N,p) (localFit hC k N p T b v)=ladd C b k N p d T v:=by
  let c:ℂ:=↑(C.S.a k ^ d:ℝ)
  change c • ((charts C hC d k (N,p)).symm : _ ≃ₗ[ℂ] _) (c⁻¹ • ((charts C hC d k (N,p)) (ladd C b k N p d T v)))= _
  rw [map_smul,LinearEquiv.symm_apply_apply,smul_inv_smul₀]
  have hp:0<C.S.a k ^ d:=pow_pos (C.S.a_pos _) _; unfold c; exact_mod_cast hp.ne'

-- use F.grades bound for both
omit hr hn in
private lemma nf (t : ℝ) (ht:0≤t) (β:ℕ) (q:ℂ) : ‖((↑(t^β):ℂ)*q)‖ = t^β * ‖q‖ := by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg ht _)]
omit hr hn in
private lemma filter_bound (i : (F).Index) : (F|>.grades i).2 ≤ d:=by
  exact Planned.PrimaryIntegral295.Film.second_fits F i
omit hr hn in
private lemma rateWeight {b t:ℝ}(hb:0≤b)(ht:1≤t)(hh:b≤t)(v:C.label d) :
    mass C d (weightTag C d b v) ≤ t^d*mass C d v := by
  unfold mass Labels.Frame.coeffSize; rw [mul_sum]; apply sum_le_sum; intro i _
  change ‖(b:ℂ)^(F|>.grades i).1*v i‖ ≤ _
  rw [← Complex.ofReal_pow,nf b hb]; gcongr
  exact (pow_le_pow_left₀ hb hh _).trans (pow_le_pow_right₀ ht ((F).bound i))
omit hr hn in
private lemma rateSlots {b t:ℝ}(hb:0≤b)(ht:1≤t)(hh:b≤t)(v:C.label d) :
    mass C d ((F).scaled b v) ≤ t^d*mass C d v := by
  unfold mass Labels.Frame.coeffSize; rw [mul_sum]; apply sum_le_sum; intro i _
  rw [Labels.Frame.scaled_apply,nf b hb]; gcongr
  exact (pow_le_pow_left₀ hb hh _).trans (pow_le_pow_right₀ ht (filter_bound i))
-- also use `read` cost ≤ (3/2)*awake (reverse of solve bound)
include hC h
private lemma fit (v:C.label d) : T (ladd C b k N p d T v) = (F).scaled (shrink C k N p)⁻¹ (weightTag C d b v):=by
  unfold ladd; rw [dif_pos (h.bijective C hC hr hn _)]
  let W:=LinearEquiv.ofBijective T (h.bijective C hC hr hn _)
  exact W.apply_symm_apply _
-- shrink ≤ 2
omit hr h in
lemma shrink_current : shrink C k N p ≤ 2:=by
  let β := C.path.β N p k; let c := (A).clock.hatBeta k; let s := (A).clock.monitor k
  have hb : 0<β := Overlay.beta_positive hC.wilson hn; have hc : 1 < c := (A).fits.delayed _
  have hx : c / 2 ≤ β := (hC.wilson.represents N p k hn).band.1
  have hs : 1 ≤ s := Real.one_le_exp (sq_nonneg _)
  have ht : 0 < Real.sqrt c:= Real.sqrt_pos.2 (zero_lt_one.trans hc)
  have hu : 0 < Real.sqrt β := Real.sqrt_pos.2 hb
  change (Real.sqrt β)⁻¹/((Real.sqrt c)⁻¹*s) ≤ _
  field_simp
  have hh : Real.sqrt c ≤ Real.sqrt β * 2 :=by nlinarith only [Real.sq_sqrt (zero_lt_one.trans hc).le, Real.sq_sqrt hb.le,hx, hu,ht]
  nlinarith only [hh,le_mul_of_one_le_right hu.le hs]

theorem priced (hb:1≤b) (v:C.label d):
    mass C d (localFit hC k N p T b v) ≤ 2*(2*(A).clock.monitor k)^d * b^d * mass C d v:=by
   let t:= ladd C b k N p d T v; let s:= (A).clock.monitor k
   have hh: 1 ≤ s := Real.one_le_exp (sq_nonneg _); have hc:1 ≤ 2*s:=by linarith
   have ht:=shrink_pos C hC hn p
   rw [local_awake hC hr hn]
   calc
     mass C d (awake C d k N p t) ≤ 2 * mass C d (T t) := h.cost C T _
     _ ≤ 2*((2*s)^d* (b^d * mass C d v)):=by
       dsimp only [t]; rw [fit hC hr hn h b v]
       gcongr
       exact (rateSlots (inv_pos.mpr ht).le hc (shrink_min C hC hn p) _).trans (mul_le_mul_of_nonneg_left (rateWeight (zero_le_one.trans hb) hb le_rfl _) (by positivity))
     _ = _ :=by ring

theorem unpriced (hb:1≤b) (v:C.label d):
    mass C d v ≤ 2^d * (3/2) * mass C d (localFit hC k N p T b v):=by
   let r:= shrink C k N p; let z:=ladd C b k N p d T v
   have ht:=shrink_pos C hC hn p
   have he : mass C d (T z) ≤ 3/2*mass C d (awake C d k N p z):=by
      have hi:= size_triangle F (T z) (awake C d k N p z); rw [size_sub_rev] at hi; unfold mass; linarith only [hi,h.score z]
   have hp:v=weightTag C d b⁻¹ ((F).scaled r (T z)):=by
      rw [poured hC hr hn b T h v, ← LinearMap.comp_apply,← facsimile]
      rw [inv_mul_cancel₀ (show b ≠ 0 from (zero_lt_one.trans_le hb).ne')]; ext j; simp [weightTag]
   calc
     _ = mass C d (weightTag C d b⁻¹ ((F).scaled r (T z))) := congr_arg (mass C d) hp
     _ ≤ (1:ℝ)^d * (2^d * mass C d (T z)) := by
       apply (rateWeight (inv_nonneg.mpr (zero_le_one.trans hb)) le_rfl (inv_le_one_of_one_le₀ hb) _).trans
       exact mul_le_mul_of_nonneg_left (rateSlots ht.le (by norm_num) (shrink_current hC hn) _) (by simp)
     _ ≤ _ :=by rw [one_pow,one_mul, local_awake hC hr hn,mul_assoc]; gcongr
end YM.RG12.Arche
