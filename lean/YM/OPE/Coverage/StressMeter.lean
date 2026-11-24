import YM.OPE.Coverage.DemandStress
import YM.OPE.Coverage.Centered
import YM.OPE.Coverage.Tariff

/-!
## Prepare the actual stress as a measured weak slot at engineering price
through the log-dense regime

Use **flux normalization** and simultaneous successor/probe demands before
extracting the differential curve; use the hierarchy's *same* centered
stress in the pressure factor, adding back the expectation explicitly.
No scale-dependent definition of the tensor. No all-field, positive-order
or regulator-removed PT conclusion in this theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.OPE.Coverage
open Function Set Filter Table Extraction Ward Climb Spec Maxwell Org Maxwell Next.UVStress Extra Pert
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
open WeakScaling
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U :Final C F S)
variable {R:ℝ}{d D D₀ N n m:ℕ}{P:MaxwellData C}{r:ℕ→ℝ}(p:Stored U r D N R)
set_option quotPrecheck false
local notation "Φ" => U.sector.derivatives
local notation "Y" => reCenter S (U.sector.energy)
local notation "𝒟" => fun e=>Nonempty (YM.Spin.change S e)
local notation "Τ" => Bel C.book
variable (earlier : ∀ d, Nonempty (YM.Spin.change S d))
variable (b:Curve U.sector.derivatives P.T.W (U.room.kernel.spin) (P.hT.spin) N d R) (hb : b.r = p.path) (hq : ∀ v : (Bel C.book).Field 4, ∃ f:ℕ→ (Bel C.book).Field 4, Tendsto f atTop (𝓝 v) ∧ (fun i=> b.X i 4 v) =ᶠ[atTop] fun i=> p.maps i 4 (f i))
variable (hf : ∀ᶠ i in atTop,Bijective (p.maps i 4)) (hd : 4 ≤ d)
variable (hp:∃ c:ℝ, ∀ᶠ k in atTop,‖b.pull (reCenter S (U.sector.energy)) k‖*(b.r k)^4 ≤ c)
include hq earlier hf
local notation "Δ"=> fun j=> (oldChart U p.toShelf 4 j (earlier (show ℕ from 4)))
private lemma relative_bound : ∃ c:ℝ,∀ᶠ i in atTop,∀ (v : (Bel C.book).Field 4), ‖(Δ i).symm (b.X i 4 v)‖ ≤ c * ‖v‖:=by
    obtain ⟨k,h,hG⟩: ∃ k:ℕ→ ((Bel C.book).Field 4→ₗ[ℂ] (Bel C.book).Field 4), Tendsto (fun i=>(k i).toContinuousLinearMap) atTop (𝓝 (1:((Bel C.book).Field 4)→L[ℂ] ((Bel C.book).Field 4))) ∧ ∀ i v,k i v=(Δ i).symm (b.X i 4 v):= by
      let k i:= ((Δ i).symm.toLinearMap.comp (b.X i 4).toLinearMap)
      refine ⟨k,Dash.fit_plane (ℱ:=atTop) k LinearMap.id (fun v=>?_), fun _ _=>rfl⟩
      rcases hq v with ⟨z,h,hz⟩; exact h.congr' (hf.and hz |>.mono fun i ⟨hf,hz⟩=> (Δ i).injective (by
        change Δ i (z i)=Δ i ((Δ i).symm (b.X i 4 v)); erw [LinearEquiv.apply_symm_apply, show Δ i (z i)=(p.maps i 4) (z i) from LinearMap.congr_fun (old_agrees U p.toShelf earlier i 4 hf) _]; exact hz.symm))
    refine ⟨2,(h.norm.eventually (gt_mem_nhds (?hh : ‖(1: (Bel C.book).Field 4→L[ℂ] (Bel C.book).Field 4)‖ < 2))).mono (fun i hi v=> by rw [← hG]; exact ((k i).toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg v)))⟩
    case hh => exact (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i => by simp)).trans_lt one_lt_two

include hp hb hd
lemma shelf_recenter (he:Fine r) (a c:Axis): Poly r (fun k=> (Δ k).symm (r k^4 • ((Y) a c))):=by
    let v(k:ℕ):=(b.pull (reCenter S (U.sector.energy)) k) a c; let z i:= (b.X i 4).symm ((↑(p.path i):ℂ)^4 • (Y) a c); obtain ⟨B,hB⟩:= hp
    have he': Poly r (fun i=>(Δ i).symm (b.X i 4 (z i))):=by
       obtain ⟨e₁,hc⟩:=relative_bound U p earlier b hq hf
       apply Poly.absBound he (A:= |e₁| *(max 0 B))
       filter_upwards [hc,hB] with i hi hh
       refine (hi _).trans (mul_le_mul (le_abs_self _) ?_ (norm_nonneg _) (abs_nonneg _))
       have hG:= ((norm_le_pi_norm ((b.pull (reCenter S U.sector.energy) i) a) c).trans (norm_le_pi_norm (b.pull _ i) a) : ‖v i‖ ≤ ‖b.pull (reCenter S (U.sector.energy)) i‖)
       have hv: z i = ((p.path i)^4) • v i:=by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; change _ = (↑(p.path i ^4):ℂ) • v i; rw [Complex.ofReal_pow]; exact (b.X i 4).symm.map_smul ..
       rw [hv,norm_smul,Real.norm_of_nonneg (pow_nonneg (p.fades.1 i |>.le) _),mul_comm]; exact ((mul_le_mul_of_nonneg_right hG (pow_nonneg (p.fades.1 i |>.le) _)).trans ((hb ▸ hh))) |>.trans (le_max_right ..)
    refine ((ratio_le p he).pow 4 he |>.smul he').congr (Eventually.of_forall fun i=>?_)
    dsimp only [z]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),LinearEquiv.apply_symm_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),← map_smul]
    congr 1; push_cast; rw [div_pow]; push_cast; rw [smul_smul]; congr 1; apply div_mul_cancel₀; exact (pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr ((p.fades.1 i).ne')) : (↑(p.path i):ℂ)^4 ≠ 0)

lemma shelf_stress (he:Fine r)(a c:Axis): Poly r (fun k=> (Δ k).symm (r k^4 • U.sector.energy a c)):=by
    let w (i:ℕ):= (↑(r i):ℂ)^4 * expectation S 4 ((U.sector.energy) a c)
    have hg: Tendsto w atTop (𝓝 0):=by
        have hl:= (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr he.2)).congr (f₂:=r) (fun i=> by change Real.exp (- -Real.log (r i)) = _; rw [neg_neg, Real.exp_log (he.1 _)])
        simp_rw [w]
        simpa only [Function.comp_apply,Complex.ofReal_zero,zero_pow (by decide : 4 ≠ 0),zero_mul] using ((((Complex.continuous_ofReal.continuousAt.tendsto.comp hl).pow 4).mul_const (expectation S 4 ((U.sector.energy) a c))))
    have ht: Poly r (fun i=> (Δ i).symm (w i • S.unit 4)):=by
       obtain ⟨c,hc⟩:= relative_bound U p earlier b hq hf
       refine Poly.absBound he (A:= |c| * ‖(Bel C.book).unit 4‖) ?_
       filter_upwards [hc,hg.norm.eventually (ge_mem_nhds (by simp : ‖(0:ℂ)‖ < 1)),b.graded] with i hi hg hG
       specialize hi (w i • (Bel C.book).unit 4)
       rw [map_smul,show b.X i 4 _=_ from (hG.1 _ hd).2.2] at hi
       exact hi.trans (mul_le_mul (le_abs_self _) (by rw [norm_smul]; exact (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans_eq (one_mul _)) (by exact norm_nonneg _) (abs_nonneg _))
    refine (Poly.add he (shelf_recenter U p earlier b hb hq hf hd hp he a c) ht).congr (Eventually.of_forall fun i=>?_)
    dsimp only; rw [← LinearEquiv.map_add]
    congr 1
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) _ ((reCenter S (U.sector.energy)) a c)]
    change ((↑(r i ^4):ℂ)) • _ + w i • _ = _
    dsimp only [w]; rw [Complex.ofReal_pow, mul_smul,← smul_add]
    change _ • (centering S _ _ + _) = _
    rw [value_center, sub_add_cancel,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    simp
end YM.OPE.Coverage
