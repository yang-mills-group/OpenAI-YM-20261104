import YM.RegulatorIR.Oracle.Rigging
import YM.RegulatorIR.Older.Exponential

/-! Post and pre prices in physical mixed units. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge} {X Y A B : Type}{P S:Side→Type} {α σ r l:ℝ} {q:ℕ} {t: Side}

lemma stipend (h:0<σ)(p:ℕ): ∃ c>0,∀ x:ℕ, (1+(x:ℝ)+4)^p≤ c * Real.exp (σ*x):=by
 have ht:(Real.exp (-σ)) < 1:= by simp [h]
 obtain ⟨c,hc,H⟩:= Older.cost_V (Real.exp_pos _) ht p
 refine ⟨5^p*(c+1),by positivity,fun x=>?_⟩
 have he : ((x:ℝ)+1)^p * Real.exp (-(σ*x))≤ c:=by rw [show -(σ*x)=↑x * (-σ) by ring,Real.exp_nat_mul]; exact (H x).trans_eq (by rw [one_pow,mul_one])
 rw [Real.exp_neg,← div_eq_mul_inv] at he
 calc
   _ ≤ _:= pow_le_pow_left₀ (a:=1+(x:ℝ)+4) (b:=5*(x+1)) (by positivity) (by linarith) p
   _ ≤ 5^p * (c * Real.exp (σ*x)):=by rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.exp_pos _)).mp he) (by positivity)
   _ ≤ _:=by rw [mul_assoc]; gcongr; linarith

-- transport to tariff when ports within constant of their nominal coarse root
lemma payUp {K:Quarry X A P}{F:Quarry Y B S}{V:X→Room}{U:Y→Room}{σ:ℝ}{r:ℕ} (h:0<l)(c:ℝ)
 (hC:∀ k:ℕ, (1+(k:ℝ)+4)^r ≤ c*Real.exp (σ*k))(hv:∀ i,dist (V i) (Motion.slide l (K.boom i))≤2*l)(hu:∀ i,dist (U i) (Motion.slide l (F.boom i))≤2*l){q:Layer X Y}{p:ℝ≥0∞}(Q:chestE K F σ q p): Layer.row q (Tariff.native l h r) V U (p*ENNReal.ofReal c):=by
 intro i
 apply le_trans _ (mul_le_mul_left (Q i) _)
 rw [← quota_raised]; apply quota_mono;intro j
 let d:= K.boom i;let n:=F.boom j;let x:=Motion.slide l n;let y:=Motion.slide l d; let k:= Laurent.size (d-n)
 have hY:dist y x ≤ l*k:=by
    rw [dist_eq_norm]; unfold x y;rw [← _root_.map_sub]; apply (pi_norm_le_iff_of_nonempty _).mpr; intro t; rw [Real.norm_eq_abs]; change |l*((d-n) t:ℝ)|≤ _; rw [abs_mul,abs_of_nonneg h.le]; apply mul_le_mul_of_nonneg_left _ h.le
    exact_mod_cast (show |(d-n) t|≤ (k:ℤ) from Int.natCast_natAbs _ ▸ (by exact_mod_cast (FreeResolvent.own_size (d-n) t) : ((d-n) t).natAbs ≤(k:ℤ)))
 have hp:dist (V i) (U j)≤ l*(k+4:ℝ):=by
   calc
      _ ≤ _:= dist_triangle (V i) y (U j)
      _ ≤ _:= add_le_add (hv i) ((dist_triangle y x (U j)).trans (add_le_add hY ((dist_comm x (U j)).trans_le (hu j))))
      _ = _:=by ring
 apply (Tariff.amount_mono h r hp).trans; unfold Tariff.amount
 rw [mul_div_cancel_left₀ _ h.ne',← ENNReal.ofReal_pow (by positivity : (0:ℝ)≤1+(k+4)), liftsE, ← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm _ c, ← add_assoc]
 exact ENNReal.ofReal_le_ofReal (hC k)
lemma shade_lo (h:0<l)(a:Axis) : ‖glint l a‖ ≤ l/2:=by
 apply (pi_norm_le_iff_of_nonempty ..).mpr; intro i
 unfold glint; simp only [Pi.smul_apply,Motion.slide_apply,Lattice.step_apply,Real.norm_eq_abs,smul_eq_mul];split_ifs <;> norm_num <;> linarith [abs_of_nonneg h.le]
lemma costsG (h:0<r)(x: Long G.ColorIndex): dist (seat r x.1) (Motion.slide r ((linksQ G).boom x)) ≤2*r:=by
 unfold seat;change dist (Motion.slide r _+_) (Motion.slide r x.1.1)≤_
 rw [dist_eq_norm,add_sub_cancel_left];exact (shade_lo h x.1.2).trans (by linarith)
private lemma latter (h:0<l)(Y:Site t): ‖Motion.slide l (Lattice.lift Y)‖ ≤ l*t.val:=by
 apply (pi_norm_le_iff_of_nonempty ..).mpr; intro j
 rw [Real.norm_eq_abs, Motion.slide_apply,abs_mul,abs_of_nonneg h.le]
 apply mul_le_mul_of_nonneg_left _ h.le
 -- abs proof Int
 have H:= lift_centers Y j
 rw [abs_le]; exact_mod_cast (show -(t.val:ℤ) ≤ Lattice.lift Y j ∧ Lattice.lift Y j ≤ t.val from by omega)
lemma true_boom (h:0<l)(hv:r=l*t.val)(s:Cover)(u:Site t) : dist (Motion.slide l (child t s u)) (Motion.slide r s) ≤ r:=by
 unfold child;rw [_root_.map_add,turns_site, ← hv, dist_eq_norm,add_sub_cancel_left]; rw [hv]; exact latter h u
lemma costsB (h:0<l)(hv:r=l*t.val)(x:Long G.ColorIndex): dist (seat l x.1) (Motion.slide r ((blockQ G t).boom x))≤2*r:=by
 rcases x with ⟨⟨x,y⟩,v⟩; obtain ⟨⟨s,u⟩,rfl⟩:=reachesR t x
 let x:=child t s u; have hp: (blockQ G t).boom ((x,y),v)=s:=congr_arg Prod.fst (landFull t s u (coord y,v))
 apply le_trans (dist_triangle _ (Motion.slide l x) _); rw [hp,seat,dist_eq_norm]; dsimp only
 unfold x;rw [add_sub_cancel_left]
 have ht:r≥l:=hv.symm ▸ (show l≤ l*t.val from le_mul_of_one_le_right h.le (by exact_mod_cast t.property))
 have hh:= true_boom h hv s u; have hl:=shade_lo h y; linarith
lemma costsC (P:Patch) (h:0<l)(hv:r=l*P.L.val)(x:RegulatorIR.Gain.Point G): dist (Gain.pointS l x) (Motion.slide r ((gardens P G).boom x))≤ 2*r:=by
 rcases x with ⟨x,y⟩; obtain ⟨⟨s,u⟩,rfl⟩:= reachesR P.L x
 let z:=child P.L s u; have ht:(gardens P G).boom (z,y)=s:= congr_arg Prod.fst (landFull P.L s u y)
 rw [ht]; apply (true_boom h hv s u).trans; have he:0<r:=by rw [hv]; positivity
 linarith
end YM.RegulatorIR.Oracle
