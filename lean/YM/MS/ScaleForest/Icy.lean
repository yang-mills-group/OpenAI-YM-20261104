import YM.MS.ScaleForest.HeatScale
/-!
# Pure pole times actual integrated complement

At a bridge in a quotient with no explicit loops, and multiplication by a
child pure Laurent monomial times a local homogeneous vertex. Provides the
usual elementary form, with all scales at log length and IR cutoff *still in
place*. For quotient components with loops use the distribution law instead;
there can be z-dependence even in the complement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {V : GraphSum G true 4} {b : Bool} {h n ℓ : ℕ} {W : Mob G} {r t : ℤ}

theorem plow_scale (c : ℂ) (t : ℝ) (d : ℂ) (w : Mob G) : plow c t (d • w)= d• plow c t w := by
  rw [ ← cert,map_smul,cert]

theorem bridge_scale (K : Rip G) (hv : reverseF K) (F H : Mob G) (c : ℂ) : bridgeG K F (c • H) = c • bridgeG K F H := by
  rw [bridgeG_eq hv, bridgeG_eq hv, ← schedule,← schedule, map_smul]

/-- A version with cutoff identity included. -/
theorem regulated_scale (W : Mob G) (a s : ℝ) (h ℓ : ℕ) (z c : ℂ) :
    regulated a s z h ℓ (c•W) = c•regulated a s z h ℓ W := by
  unfold regulated finiteIntegral
  rw [ show (fun m (w:Legs (Shore G m))=> ∫ t in a..s, plow (vamp z h ℓ) t (c•W) m w) =
        c • (fun m (w:Legs (Shore G m))=> ∫ t in a..s, plow (vamp z h ℓ) t W m w) from ?_]
  · split_ifs; simp only [add_zero]
    unfold belowCut; rw [smul_add]; simp_rw [Finset.smul_sum,t_pose];
    refine congr_arg₂ _ rfl (Finset.sum_congr rfl fun j _ => ?_)
    rw [smul_comm _ c,smul_comm _ c]
  funext m w
  simp_rw [plow_scale,Pi.smul_apply,smul_eq_mul,intervalIntegral.integral_const_mul]

theorem integrate_scale (hW : kPrice W) (hU : Shine.Wind (fun t => plow (-(h:ℂ)) t W) atBot 0)
    (c z : ℂ) : scaleIntegral z h 0 (c•W)= c • scaleIntegral z h 0 W := by
  funext m w
  have hz := uv_limit_aux (W:=W) (z:=z) hW (ell:=0) (fun _ => hU) (by simp) (by simp) 0
  rw [posing,← evaluated hW (fun _ => hU) (by simp) (by simp)] at hz
  unfold scaleIntegral; simp_rw [regulated_scale,Pi.smul_apply]
  exact (Tendsto.const_smul (hz m w) _).limUnder_eq

/-- Combine an unmarked vertex and a monomial pole with prescribed local symbol. -/
theorem freezing (K : LineRule G) (A : LocalVertex G true 4) (B : LocalVertex G b h) (ℓ : ℕ) :
    combine b h K (classicalPage A.symbol) (collapsed (Ice ℓ B.symbol)) =
      collapsed (Ice ℓ (firstSymbol A B K)) := by
  unfold GraphSum.combine connect collapsed classicalPage collapsed
  rw [bridge_single K.half K.ok.rev, Finsupp.smul_single, Nat.add_zero,integrate_single]
  have ht := (firstSew A B K).accepted.force
  rw [first_force] at ht
  have he:= ht.force
  unfold Return at he
  simp_rw [classicalPage,collapsed,Finsupp.single_eq_same,Pi.zero_apply] at he
  congr 1; funext z
  let c := (z⁻¹^ℓ); let x:ℂ := factor b
  change scaleIntegral z h 0 (x • bridgeG K.half A.symbol (c • B.symbol))=c • firstSymbol A B K
  rw [bridge_scale K.half K.ok.rev,smul_comm x c]
  change scaleIntegral z h 0 (c • firstForce A B K)=_
  rw [integrate_scale (collapsed_kernel ht.eye).price he.exists.choose_spec,
    firstSymbol, ← scaleZero_invariant z]

theorem parade_frozen (W : Mob G) (s y : ℝ) (z : ℂ) (h ℓ : ℕ) :
    Parade (collapsed (Ice ℓ W)) h y s z = z⁻¹^ℓ • plow (-(h:ℂ)) s W := by
  rw [collapsed,page_sl,hikeP, Ice,show Pearl.weight z 0 y=(1:ℂ) from by simp [Pearl.weight,toll,amount],
    one_smul, vampV,plow_scale]

theorem one_pick_real (hx : Cap0 b t r (Ice n W)) (hm : kPrice W) : Cap0 b t r (fun _ : ℂ=> W) := by
  have ht : Pick 0 (paid n (Ice n W)) W := by simpa using (icePick (j:=0) hm (le_refl n))
  have hp (P : LeanC G) (hp : Need P) (he : To (Ice n W) P) : To (fun _ : ℂ=> W) P :=
    Eventually.of_forall (fun _ => shoreC P hp ht (he.mono fun x hx => P.smul_mem (x^n) hx))
  refine ⟨⟨⟨mer.uLive (Live.stays hm),hp _ need_true hx.fine.tune.dice⟩, hp _ need_col hx.fine.ghost,
    Eventually.of_forall fun y : ℝ => shoreR (sight G) need_eye ht ?_⟩, hp _ need_tail hx.cap⟩
  refine Eventually.mono hx.fine.sense fun i hi => ?_
  unfold paid; rw [← Complex.ofReal_pow,reality]; exact (sight G).smul_mem _ hi

def PoleVertex (T : GraphSum G b h) {W : Mob G} (n : ℕ) (he : T.instructions.pole = Ice n W)
    (hm : kPrice W) : LocalVertex G b h where
  rank := T.slots
  symbol := W
  cap := one_pick_real (he ▸ T.accepted.poleShape) hm
  scaling := by
    have hp := T.accepted.after.back 1
    rwa [he, Ice,inv_one,one_pow,one_smul] at hp
  slots := by
    have hp := T.accepted.legs_ct 1
    rwa [he, Ice,inv_one,one_pow,one_smul] at hp
end YM.MS.ScaleForest
