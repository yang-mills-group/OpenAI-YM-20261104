import YM.GradedFar.Neighbor
import YM.GradedFar.Interpose
/-!
# Formal relative field-change inputs used for the growing variant of G.1
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
variable {h:ℕ}

abbrev Operation (G:Gauge)(h:ℕ) := Sheet G h →L[ℂ] Sheet G h
local notation "Zop" => Operation G h

def stamp (G:Gauge)(h:ℕ) : (Sec G h →ₗ[ℂ] Sec G h) →ₗ[ℂ] Operation G h where
    toFun := access
    map_add' a b:= by ext1 v; exact map_add (columns G h) (a ((columns G h).symm v)) (b ((columns G h).symm v))
    map_smul' c a:= by ext1 v; exact map_smul (columns G h) c (a ((columns G h).symm v))
lemma stamp_one : stamp G h 1= 1:= by
    ext1 x; exact (columns G h).apply_symm_apply _
lemma stamped (A:Sec G h→ₗ[ℂ] Sec G h)(v:Sec G h): stamp G h A (columns G h v)= columns G h (A v):= by
    change columns G h (A ((columns G h).symm (columns G h v)))=_; rw [LinearEquiv.symm_apply_apply]
lemma price (A B:Sec G h→ₗ[ℂ] Sec G h) : stamp G h (A*B) = stamp G h A * stamp G h B:=by
    ext1 x; obtain ⟨v,rfl⟩:= (columns G h).surjective x; rw [mul_apply_eq_comp,stamped,stamped,stamped]; rfl

def stretching (G:Gauge)(h:ℕ)(t:ℝ) : Operation G h:= stamp G h (Level.Dial h t)
lemma stretch_units (i:Toon G h)(t:ℝ): stretching G h t (columns G h (theory i))=
    Extent.token t i.size • columns G h (theory i):=by rw [stretching,stamped, Level.exact₀,map_smul]
lemma stretch_mul (G:Gauge)(h:ℕ)(t u:ℝ): stretching G h t * stretching G h u = stretching G h (t+u):= by
    simp only [stretching, ← price, Level.group]
lemma flat (G:Gauge)(h:ℕ): stretching G h 0=1:=by rw [stretching,Level.flat,stamp_one]
lemma dial_coord (v:Sec G h)(t:ℝ)(i:Toon G h): (columns G h (Level.Dial h t v)) i=Extent.token t i.size * coord i v:=by
    conv_lhs=>rw [← all_sig v];
    simp_rw [map_sum,map_smul]; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Level.exact₀]
    simp_rw [map_smul, Pi.smul_apply,smul_eq_mul,columns_coord,pivotδ]; rw [Finset.sum_eq_single i];
    · simp [mul_comm]
    exacts [fun j _ hj=> by simp [hj],by simp]
lemma stretch_limit {L:ℝ}(hL:0≤L)(t:ℝ)(hm:∀ i:Toon G h,‖Extent.token t i.size‖≤ L): ‖stretching G h t‖≤ L:= by
    refine op_pay hL (fun v hv=> (width_le hL).2 (fun i=>?_))
    rw [← columns_coord,dial_coord,norm_mul]; exact
      (mul_le_mul (hm i) ((coord_le i v).trans hv) (norm_nonneg _) hL).trans_eq (mul_one _)
lemma stretch_up (G:Gauge)(h:ℕ){T:ℝ}(hT:1≤T): ‖stretching G h (-Real.log T)‖≤ T^h:= by
    have ht:0<T:=zero_lt_one.trans_le hT; refine stretch_limit (by positivity) _ (fun i=>?_); unfold Extent.token; rw [neg_neg,Real.exp_log ht,norm_pow, Complex.norm_real,Real.norm_of_nonneg ht.le]
    exact pow_le_pow_right₀ hT (size_le i)
lemma stretch_down (G:Gauge)(h:ℕ){T:ℝ}(hT:1≤T): ‖stretching G h (Real.log T)‖≤ 1:= by
    have ht:0<T:=zero_lt_one.trans_le hT; refine stretch_limit zero_le_one _ (fun i=>?_); unfold Extent.token; rw [norm_pow, Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]; exact pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.log_nonneg hT)))

def ticker (p:ℕ)(y:ℝ)(z:ℂ) := operation p z (ofPS (ϕ y))
local notation "op" => stamp G h
def firm (h:ℕ)(t:ℝ)(k:ℕ):Operation G h:= stamp G h (coeff k (Kt t h))
def fare (h:ℕ)(p:ℕ)(t:ℝ)(z:ℂ) := operation p z (firm Z M ν h t)
local notation "firm'" => firm Z M ν h
local notation "fare'" => fare Z M ν h
lemma omnibus (c:ℂ)(x y:Zop): x*(c • y)=c • (x*y):= by ext1 u; exact map_smul x c (y u)
lemma gratis (c:ℂ)(x y:Zop): (c • x)*y=c • (x*y):= rfl

def pairField (G:Gauge)(h:ℕ) : Operation G h →ₗ[ℂ] Operation G h →ₗ[ℂ] Operation G h where
    toFun u:= {toFun v:= u*v
               map_add' a b:= mul_add u a b
               map_smul' a c:= omnibus a u c}
    map_add' a b:= by ext1 v; exact add_mul a b v
    map_smul' a b:= by ext1 v; exact gratis a b v
lemma pairField_value (a b:Zop): pairField G h a b=a*b:=rfl
lemma used (p:ℕ)(t y:ℝ) : stamp G h (cropK Kt t p y h)= stretching G h t * fare' p t y:= by
    simp only [fare,firm,cropK,map_sum,map_smul,conversion,coeff_C_mul,price,stretching,
      operation, Finset.mul_sum, omnibus]

variable {A0:Gauge}
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
include H
lemma kept (t u:ℝ)(p:ℕ)(v:ℂ): stretching G h t * fare' p u v = fare' p u v * stretching G h t:=by
    simp only [fare,firm,operation,Finset.sum_mul,Finset.mul_sum,omnibus,gratis,stretching, ← price,
      Level.rise t _ ((H.dilation ν).check.ready u h _)]
lemma hands (t u:ℝ): firm' (t+u) = pairW (pairField G h) (firm' t) (substitute (ϕ t) (firm' u)):=by
    obtain ⟨_,hv⟩:= (H.dilation ν).check.additive t u; specialize hv h
    rw [old_g u (Kt t h) ((H.dilation ν).check.ready t h)] at hv; funext i
    simp only [firm,hv,coeff_mul,MS.Book.Convolve.paired,Reg.Point.stepV, coeff_mk, rules,map_sum, map_smul, pairField_value,price,Finset.mul_sum,omnibus]
lemma days (t u:ℝ) : ofPS (ϕ (t+u))= substitute (ϕ t) (ofPS (ϕ u)) := by
    funext i; rw [(H.dilation ν).check.additive t u|>.1, ← Constants.actual_subst _ _ ((H.dilation ν).check.led t).start]; exact coeff_mk ..

omit H
variable {Iota:Type*} {L x:Iota→ℝ}
lemma feasible_cash (f:ℝ→ℂ) (h:Rhythm f)(hv : Charge L (fun i=> (x i :ℂ))): Charge L (fun i=> f (x i)):= by
    obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp h; exact Charge.across hv
lemma plan_cost {y:ℝ} {A:Sec G h→ₗ[ℂ]Sec G h}(hp:0≤y)
    (H:∀ i j, ‖coord i (A (theory j))‖ ≤ y) : ‖op A‖ ≤ Fintype.card (Toon G h)*y:= by
    refine op_pay (mul_nonneg (Nat.cast_nonneg _) hp) ?_; intro v hv
    refine (width_le (mul_nonneg (Nat.cast_nonneg _) hp)).mpr ?_; intro i
    conv_lhs=> rw [← all_sig v];
    simp_rw [map_sum,map_smul]; exact (norm_sum_le ..).trans ((Finset.sum_le_sum
      (g:=fun _=>y) (fun i _=> by rw [norm_smul]; exact (mul_le_mul ((coord_le i v).trans hv) (H ..) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))).trans_eq (by simp))
include H
lemma field_cost (h:ℕ)(hv:Charge L (fun i=> (x i:ℂ))) : Feasible (fun i=> firm Z M ν h (x i)) L:=by
    intro k; have hi (i j:Toon G h): Charge L (fun a=> coord i (coeff k (Kt (x a) h) (theory j))):=
      feasible_cash _ ((H.dilation ν).check.proper h k (theory j) ( (Theater.Daylight (Press.portDeck G) h).coord i )) hv
    obtain ⟨q,hq⟩:= (poly.all (a:=fun (ij: Toon G h × Toon G h) i=>
      ‖coord ij.1 (coeff k (Kt (x i) h) (theory ij.2))‖) (fun j=> hi j.1 j.2)).exists
    obtain ⟨C,hC,hq⟩:= ((eventually_ge_atTop 0).and hq).exists
    exact ⟨Fintype.card (Toon G h)*C, by positivity,q,fun i=>(plan_cost (by positivity)
      (fun a b=> hq i (a,b))).trans_eq (mul_assoc _ _ _).symm⟩
lemma days_cost (hx: Charge L (fun i=> (x i:ℂ)))(k:ℕ): Feasible (fun i=> ofPS (ϕ (x i)^k)) L:=fun i=>
    feasible_cash _ (Rhythm.unit.mpr (Pace.formal.pow (f:=fun (_:Unit) t=> ϕ t) (H.dilation ν).check.smooth k i)) hx
lemma row_cost (hx: Charge L (fun i=> (x i:ℂ))) : Feasible (fun i=> ofPS (ϕ (x i))) L:= by
    have h:=days_cost Z M ν H hx 1; simp_rw [pow_one] at h; exact h
end YM.Integration.GradedFar.Neighbor
