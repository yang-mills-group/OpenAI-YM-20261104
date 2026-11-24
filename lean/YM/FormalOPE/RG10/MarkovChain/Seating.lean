import YM.FormalOPE.RG10.MarkovChain.Timetabled
/-!
 # Two-level compressed formal Gaussian transmission, not conditioning on extraneous fields
 # Does maintain fixed finite layout of trusses; these are formal coefficients
 # not distributions on the actual field. Auxiliary regulator chosen pointwise in chain; not uniform bound. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
namespace Router
local notation "Ω"=> Field (Cloth.choose T0)
local notation "V"=> Field C.choose
local notation "F"=> Cross (G:=G) S P
-- with genuine variable set $F = currently fine indices$
local notation "N" => Head C.choose
-- remember at top state can have any value but at next root choose canonical truss coordinates as compensated.
 def descendMap : (F × Head C.choose)→ₗ[ℝ] Ω := (d).toLinearMap ∘ₗ ( (LinearMap.id (R:=ℝ) (M:=F)).prodMap (importTop C.choose))
local notation "ξ"=> descendMap (S:=S) (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)
@[simp] lemma descend (x y): ξ (x,y) = d (x, place _ y):= rfl
lemma relay {u:Ticket Ω}(h:Adjacent u)(x y): Stack.read (x,send C.choose y) (boost ξ u)=Stack.read (d (x,y)) u:= by rw [caught,descend]; exact h _ _ _ (send_place ..)
-- optional impose F basis finite costs separately
 def localPin (Λ: Law Ω) : N →ₗ[ℝ] F:= pin Λ d ∘ₗ importTop C.choose
 def drift (Λ:Law Ω): F × N→ₗ[ℝ] F × N:= (LinearMap.fst ℝ F N+localPin Λ ∘ₗ LinearMap.snd ℝ F N).prod (LinearMap.snd _ _ _)
@[simp] lemma localizes (Λ:Law Ω)(x y): drift Λ (x,y)= (x+localPin Λ y,y):= rfl
lemma overcast (Λ: Law Ω)(h:Actual T0 Λ)(y:V): localPin Λ (send C.choose y) = pin Λ d y:= Actual.spans (show Law (Field (P.join C.choose H t hf)) from Λ) h (importTop C.choose (send C.choose y)) y (send_place ..)

 def nearest (Λ:Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ]: Ticket (F × N) →+ Ticket N:= throughPrice ((Papers.splitting (fast Λ d) μ).comp (translation (drift Λ)).toLinearMap).toAddMonoidHom
lemma purest (Λ: Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](a:Ticket (F×N))(h: incline a): incline (nearest Λ μ a):= by unfold incline nearest throughPrice; unfold incline at h; rw [←coeff_zero_eq_constantCoeff_apply]; simp [h,singly]
lemma locally (Λ: Law Ω)(μ : Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](A:Ticket (F×N))(i:ℕ)(y:N): (coeff i (nearest Λ μ A)).val y = (fast Λ d).average μ fun x=> (coeff i A).val (x+localPin Λ y,y):= by
 unfold nearest throughPrice; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk, LinearMap.toAddMonoidHom_coe]; exact (Penn (fast Λ d) μ _ y) -- defeq fusion pair

lemma locally_matches (Λ:Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ] (h:Actual T0 Λ){u:Ticket Ω}(hp:Adjacent u): reclose Λ d μ u = transmit C (nearest Λ μ (boost ξ u)):= by
 apply PowerSeries.ext; intro i; apply Subtype.ext; funext y
 have he:= fun z=> congr_arg (coeff i) (relay hp z y); simp_rw [reading_term] at he
 unfold transmit boost reclose throughPrice; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_map,coeff_mk,LinearMap.toAddMonoidHom_coe]
 change (partialMean Λ d μ _).val _= (coeff i (nearest Λ μ _)).val (send C.choose y)
 rw [displayed,locally,overcast Λ h]; exact congr_arg ((fast Λ d).average μ) (funext fun x=> (he (x+ pin Λ d y)).symm)

 def delivery (Λ:Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](A W: Ticket (F × N)): Ticket N:= nearest Λ μ (W*A) * Return (nearest Λ μ W)
lemma normal (Λ:Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ] (A: Ticket (F × N)){W: Ticket (F × N)}(h:incline W): nearest Λ μ W * delivery Λ μ A W= nearest Λ μ (W*A):= by rw [delivery,mul_left_comm (nearest Λ μ W),spend_it (purest Λ μ _ h),mul_one]
lemma grows {T:Cloth L}(A B:Ticket (Head T.choose)): transmit T (A*B)= transmit T A* transmit T B:= _root_.map_mul ..
lemma local_delivery (Λ:Law Ω) (μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](hh:Actual T0 Λ) {A W: Ticket Ω}(ha:Adjacent A)(hv:Adjacent W)(h:incline W): delivered Λ d μ A W= transmit C (delivery Λ μ (boost ξ A) (boost ξ W)):= by
 apply (worth (born_transfer Λ d μ h)).mul_left_cancel
 rw [junior Λ d μ A h,locally_matches Λ μ hh (receive hv ha), _root_.map_mul (boost ξ) W,locally_matches Λ μ hh hv,←grows,normal Λ μ _ (preserve_boost _ h)]

/-- insertion at two rows only. `handle` uses the composite factor criterion; both sides divide
    by full normalizations. The transmitted message can be computed from compressed pair tickets. -/
lemma authentic (Λ:Law Ω) (μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](hh:Actual T0 Λ) {A W: Ticket Ω}(ha:Adjacent A)(hv:Vault T0 W)(h:incline W): delivered Λ d μ A W= transmit C (delivery Λ μ (boost ξ A) (boost ξ (handle W))):= (surround Λ μ W A h).trans (local_delivery Λ μ hh ha (tip (show paired W from (by rw [Vault] at hv; exact hv.1)) h) (seat h))
lemma onward (Λ:Law Ω)(μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](hh:Actual T0 Λ){u:Ticket Ω}(hv:Vault T0 u)(h: incline u): reclose Λ d μ u= transmit C (nearest Λ μ (boost ξ (handle u))) * boost (coarse d) u:= by rw [Vault] at hv; rw [rWeight _ _ _ h, locally_matches Λ μ hh (tip hv.1 h)]
lemma advance (Λ:Law Ω) (μ:Measure (Cross (G:=G) S P))[Measure.IsAddHaarMeasure μ](hh:Actual T0 Λ){u:Ticket Ω}(hv:Vault T0 u)(h: incline u): Vault C (reclose Λ d μ u):= by rw [onward _ _ hh hv h]; rw [Vault] at hv; exact Vault.mul (vaulted C (written C _)) hv.2
lemma forever (Λ:Law Ω)(hh: Actual T0 Λ): Actual C (rest Λ d):= Actual.revenue (show Law (Field (P.join C.choose H t hf)) from Λ) hh
end Router
end YM.FormalOPE.RG10.MarkovChain
