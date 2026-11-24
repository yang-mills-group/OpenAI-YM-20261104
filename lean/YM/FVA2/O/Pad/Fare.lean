import YM.FVA2.O.Tune.Reach
/-!
# Pricing a local point generator to use in the FAR exact-term subtraction

Use in `Pad` to allow extending to other (integer) dimensions even for
these auxiliary unphysical operators. Doesn't add them to the final alphabet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Pad
open MS Function Filter Set Finset MS.Plane MeasureTheory Real Metric
open Momentum Heat Koszul Flux High Landau Detect MS.Color Book Signal Arts Alps MS.Local.Physical
open Wire
open scoped Topology ContDiff Interval
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{n k m:ℕ}{h b:ℤ}{F:Law G}
-- specialize closedBall estimate for Shape 
lemma Parse {f:E→ℂ}(H:Shape f h){v:ℝ}(hp:0<v) (t:E)(j:ℕ): ‖iteratedFDeriv ℝ j f ( v • t )‖ = v^(h-(j:ℤ)) * ‖iteratedFDeriv ℝ j f t‖:= by
    obtain hD:=Rake.era_spec (n:=-h) hp H.smooth j t; rw [show Rake.era v f (-h) =f from ?_] at hD; swap
    · funext x; unfold Rake.era; rw [H.scale,smul_smul,← zpow_add₀ hp.ne',neg_add_cancel,zpow_zero,one_smul]
    rw [hD,← mul_assoc,← zpow_add₀ hp.ne',show (h-(j:ℤ))+((j:ℤ)+-h)=0 from by abel, zpow_zero,one_mul]
lemma cost [FiniteDimensional ℝ E]{f:E→ℂ}(H:Shape f h): Arc.veg 0 (fun (_:Unit)=> f) 1:= by
    let K:=Arc.path (0:Arc.UScale Unit); refine ⟨fun _=> H.smooth,fun j=>?_⟩; let k:=h.toNat; let V(p:E):=‖iteratedFDeriv ℝ j f p‖; let S:=closedBall (0:E) 1; haveI : ProperSpace E:= FiniteDimensional.proper ℝ E; obtain ⟨C,hC⟩:= ((isCompact_closedBall (0:E) 1).image (show Continuous V from (H.smooth.continuous_iteratedFDeriv (m:= j) (by exact_mod_cast le_top)).norm )).bddAbove; have hv:∀ p∈S, V p≤C:= fun p hp=> hC ( Set.mem_image_of_mem V hp ); let D:= max C 1 ; have hD:0<D:= lt_max_of_lt_right zero_lt_one; refine ⟨ D,hD,k,fun i p _=>?_⟩; have hw: K.full.cheap i p=1+‖p‖:= by simp [K,Scale.full,Arc.path,Scale.weight]
    change V p ≤ D*K.full.cheap i p ^k * ((1:ℝ)*1^ j); rw [hw,one_pow,mul_one,mul_one]; rcases le_or_gt ‖p‖ 1 with h|h; · exact ( (hv p (Metric.mem_closedBall.mpr (by simpa using h))).trans ( le_max_left .. ) ).trans ( le_mul_of_one_le_right hD.le (one_le_pow₀ (by simp)) )
    let q:ℝ:= ‖p‖; let u:= q⁻¹ • p; have hhq:0<q:= zero_lt_one.trans h; have hK: u∈S:= Metric.mem_closedBall.mpr (show dist u 0≤1 from by simp only [dist_zero_right,u,norm_smul, norm_of_nonneg (inv_pos.mpr hhq).le]; exact ( inv_mul_cancel₀ hhq.ne' ).le)
    have hV:= (hv u hK).trans (le_max_left C 1)
    apply le_trans (le_of_eq (show V p=q^(_-(j:ℤ))*V u from Eq.trans (congr_arg V ( smul_inv_smul₀ hhq.ne' p ).symm) (Parse H hhq u j) )); rw [mul_comm D]; refine mul_le_mul ?_ hV (norm_nonneg _) (by positivity); have htq: (1+q)^k= (1+q)^((k:ℤ)):= by rw [zpow_natCast]
    rw [show (1+‖p‖)^k= (1+q)^k from rfl,htq]; apply (zpow_le_zpow_right₀ h.le ?_ ).trans ( zpow_le_zpow_left₀ (by omega) hhq.le (show q≤1+q from le_add_of_nonneg_left zero_le_one) ); unfold k; omega
lemma form_stem (X:Law G)(n:ℕ)(he:Form X wfield (n:ℤ) false)(l: Legs ( Shore G 0 ) )(x:ℝ) : amount (-(n:ℂ)+(mass l:ℂ)) x * X (sr x l)=X l:= by
    let q:(ℤ):=(n:ℤ) - fieldDim wfield l; have hv:= (he ℝ (ray l) (fun i=>Bool.noConfusion i)).scale (exp x) 1; unfold fieldVal at hv; rw [smul_eq_mul,mul_one, ray_dim, ray_sail, ray_go] at hv; change X (sr x l)=(exp x)^q • X l at hv; have hp:=exp_pos x; rw [hv]; rw [show -(n:ℂ)+(mass l:ℂ)=((-q:ℝ):ℂ) from by push_cast [mass,q]; ring,amount_mint, mul_comm (-(q:ℝ)), Real.exp_mul,← Int.cast_neg,Real.rpow_intCast, Complex.ofReal_zpow ]; rw [Complex.real_smul,Complex.ofReal_zpow, ← mul_assoc, ← zpow_add₀ (by exact_mod_cast hp.ne'),neg_add_cancel,zpow_zero,one_mul]
lemma initial_p (X:Law G)(n k:ℕ)(he:X∈ Local.Physical.Lease G (n:ℤ) k b) : Halo.Pace (n:=0) X n b (k:ℤ):= by
    obtain ⟨hv,H,h⟩:= lease_one.mp he; refine ⟨ fun E _ _ _ w=> cost (H E w (fun i=>Bool.noConfusion i)), form_stem X n H, (room X b).mp hv|>.1.weight, fun l hl=> hv.ghost l (fun i=>Bool.noConfusion i) hl, fun i=> hv.real' i (fun i=>Bool.noConfusion i), fun l hl=> h l (fun i=>Bool.noConfusion i) (by omega) ⟩
end YM.FVA2.O.Pad
