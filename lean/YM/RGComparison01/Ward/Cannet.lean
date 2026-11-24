import YM.RGComparison01.Ward.Cabri

/-!
# Link variation cost for unfrozen modes

 Small scaled ball. Explicit j (current finite order). Uniform over t parameter on
 gauge (angles), uses no controls on variation of t. Domain purchase for this
 rescaling is paid AFTER these calls in the schedule. Next inverse costs are
 evaluated at incoming beta (not calendar beta); finance at Agenda.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter MeasureTheory RG Pressure Pressure.Stores Pressure.Tube Gauge Wilson
open Lattice Next.Fluctuations Push Push.Uniform Push.AbsoluteSums Precision Exterior
open Work.E03 Work.F03 ConnectedActivityE6 SliceRows Blaze Brush Metric
open scoped Matrix.Norms.Frobenius Topology ContDiff InnerProductSpace Classical BigOperators
variable {G:Gauge}{c:Side}{j k :ℕ}{p r u d a A:ℝ}
section
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma growth (f:E→F) (hj:1 ≤ k)(h:∀ x, ‖x‖≤p → Brush k u 1 f x)(x:E) (hx:‖x‖≤p): ‖f x-f 0‖ ≤ u*‖x‖:= by
  let s:= closedBall (0:E) p; have hp y (hy:y∈s) : Brush k u 1 f y:= h y (by simpa using mem_closedBall.mp hy)
  have hv:= (convex_closedBall (0:E) p).norm_image_sub_le_of_norm_fderiv_le (fun y hy=> (hp y hy).smooth.differentiableAt (by exact_mod_cast (by omega : k ≠ 0)))
    (fun y hy=> by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (hp y hy)).inside 1 hj) (Metric.mem_closedBall_self ((norm_nonneg _).trans hx))
    (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hx))
  rwa [sub_zero] at hv

variable [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma tuned (f:E→F)(x:E)(hr:0<r)(ht:r≤1)(h:Brush k u 1 f x) (hv:‖f x‖ ≤ u*r) : Brush k (u*r) r⁻¹ f x:= by
  refine ⟨h.smooth,(inv_pos.mpr hr).le,?_⟩; rintro (_|i) hi
  · simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hv
  apply ((Brush.offer.1 h).inside _ hi).trans
  have he:1 ≤ r⁻¹ := one_le_inv₀ hr|>.mpr ht
  rw [pow_succ',←mul_assoc, mul_assoc u, mul_inv_cancel₀ hr.ne',mul_one]; exact le_mul_of_one_le_right h.nonneg (one_le_pow₀ he)

lemma liftD (f:E→F) (x:E) (h:Brush k u (a*d) f x)(hp:1≤a)(hd:0≤d): Brush k (a^k*u) d f x:= by
   refine ⟨h.smooth,hd,fun i hi=> ?_⟩; refine (h.order i hi).trans ?_; rw [mul_pow,←mul_assoc,mul_comm u]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp hi) h.nonneg) (pow_nonneg hd _)
def evolCost (k:ℕ)(u:ℝ):=(1+u)^k*k.factorial

lemma liftR (f:E→F)(V:F→G)(x:E)(hr:0<r)(hp: r ≤ p)(hf:Brush k (u*r) r⁻¹ f x) (ha:Brush k A p⁻¹ V (f x)) : Brush k (evolCost k u*A) r⁻¹ (V ∘ f) x:= by
  let L:= r • ContinuousLinearMap.id ℝ F
  let Z y:=r⁻¹ • f y
  have hL : ‖L‖≤p:=by
    unfold L; rw [norm_smul,Real.norm_of_nonneg hr.le]; exact (mul_le_of_le_one_right hr.le ContinuousLinearMap.norm_id_le).trans hp
  have he i: L (Z i) = f i:= by simp [L,Z,hr.ne',smul_smul]
  have hp' := (Brush.reading L ((he x).symm ▸ ha) hL); rw [inv_mul_cancel₀ ((hr.trans_le hp).ne')] at hp'
  have h' := hf.smul r⁻¹; rw [norm_inv,Real.norm_of_nonneg hr.le,show r⁻¹*(u*r)=u from by field_simp] at h'; change Brush k u _ Z x at h'
  have hc:= liftD _ _ (h'.pine hp') (by have h:= h'.nonneg; linarith) (inv_nonneg.mpr hr.le); rw [←mul_assoc] at hc; exact hc.shimmy (Eventually.of_forall fun i=> congr_arg V (he i).symm)
end

variable {j:ℕ} {p r u : ℝ}
local notation "T"=> Uniform.Primary c G
local notation "Y"=> Positions (Uniform.Primary c G)
local notation "R"=> (royalty G)
abbrev awake (y:Positions (Uniform.Primary c G)):= represent (tint G _ y)
@[simp] lemma awake_zero : awake (0:Y)=1 := by simp [awake]
lemma gates (G:Gauge)(k:ℕ) : ∃ d≥0,∀ c:Side,∀ y:Positions (Uniform.Primary c G),‖y‖≤1→ Mode Ward.awake y k d:= by
  obtain ⟨v,hv,hh⟩:= expCost G k (Uniform.shade G)
  let d:= (1+k.factorial*v)*(1+Uniform.shade G)
  have hp:= Uniform.shade_pos G
  refine ⟨d,by unfold d; positivity,fun c z hx=> ⟨by unfold d; positivity,fun i=> ?_⟩⟩
  let Q := tint G (Body 1 c); let L: Positions (Uniform.Primary c G) →L[ℝ] G.Color := (ContinuousLinearMap.proj (pole i)).comp Q.toContinuousLinearMap
  have he: ‖L‖≤shade G:=ContinuousLinearMap.opNorm_le_bound _ hp.le (fun i=>(norm_le_pi_norm (Q i) _).trans (Uniform.tint_le i))
  have hz : ‖L z‖ ≤ shade G:= (L.le_opNorm _).trans (by simpa using mul_le_mul he hx (norm_nonneg z) hp.le)
  have hf:= Blaze.thicken (f:=fun i=> G.lieExp (L i)) ((Brush.linearB (k:=k) _ hz (by rw [mul_one]; exact he) zero_le_one).pine (hh _ hz)); rw [mul_one] at hf
  simp_rw [awake,Work.F03.represent_link]; exact hf
namespace Visage
variable (C:Visage G k) (o:Site c)(z:G.El)
local notation "E_" => fun i:Positions (Uniform.Primary c G)=> C.encode o (awake i) z
-- this notation may fail
abbrev wing (C:Visage G k)(c:Side)(d:ℝ):= C.prices*(1+(1+R)*longitude d c.val R)^k
abbrev berth (G:Gauge)(c:Side)(k:ℕ)(d:ℝ):= royalty G*(1+longitude d c.val (royalty G))^k -- k certified
variable (hv : ∀ y: Positions (Uniform.Primary c G),‖y‖≤1→ Mode Ward.awake y k d)
include hv
lemma shot (x:Y)(hx:‖x‖≤1): Brush k (C.wing c d) 1 (E_) x:= (C.reckon o _ x z (hv _ hx)).trim
lemma drops (hk : 1 ≤ k) (x:Y)(hx:‖x‖≤ p)(he:p≤1): ‖C.encode o (awake x) z‖ ≤ C.wing c d*p:= by
    have hf:= C.shot o z hv 0 (by simp); have h':= growth (E_) hk (C.shot o z hv) x (hx.trans he); simp only [awake_zero, C.one,sub_zero] at h'; exact h'.trans (mul_le_mul_of_nonneg_left hx hf.nonneg)
lemma earnings (hk:1 ≤ k)(x:Y)(hx:‖x‖≤p)(he:p≤1): Mode (toral o z ∘ awake) x k (longitude d c.val (royalty G)) ∧ ∀ i,‖G.mat (toral o z (awake x) i)-1‖≤ Visage.berth G c k d*p:= by
    have ht i (x:Y)(hx:‖x‖≤1): Brush k (Visage.berth G c k d) 1 (fun y:Y=> G.mat (toral o z (awake y) i)) x:= ((toral_pay Ward.awake x o z (hv _ hx)).atLink i).trim
    refine ⟨toral_pay Ward.awake x o z (hv _ (hx.trans he)),fun i=> ?_⟩
    have h:= growth _ hk (ht i) x (hx.trans he); simp only [awake_zero,toral_one,Pi.one_apply,G.mat_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hx (ht i _ (hx.trans he)|>.nonneg))
end Visage
end YM.RGComparison01.Ward
