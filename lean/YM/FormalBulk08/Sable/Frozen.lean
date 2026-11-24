import YM.FormalBulk08.Sable.Snipe

/-! Split assembly. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I J:Type} [Fintype I][Fintype J]{m d:ℕ}{B σ η C:ℝ}
lemma natpow (d u:ℕ)(h:d≤u)(x :ℝ)(e:1≤x) : x^d≤x^u:=pow_le_pow_right₀ e h
lemma frozen (m u:ℕ)(hs:0<η)(hc:0≤C)(d:ℕ)(hd:d≤u):∃ B:ℝ,0≤B ∧ ∀ (L:Side), Odd L.val → ∀ S:Cross L I J, gauss S η C d →∀ (x:Biglot I) t (w:cloud m) (a:J), Knoxville (grain (fame _) 1) u (piz L x a) (partD S x.1 t d w) (B*(1+(size w:ℝ))^u *(L.val:ℝ)⁻¹^(m+d)):= by
    let U:=trimmed (Fin m×Axis) d
    choose Q hQ HQ using fun p: Grades (Fin m × Axis) => hat_pulp p
    let A:ℝ:=sack u η * (Real.exp (η*9)*(Fintype.card J*C))^m
    let z:ℝ:=1+m*9; let P:ℝ:= sack u η * (Fintype.card J*C)
    have ht:= sack_pos u hs
    have hP:0≤ P:= by unfold P; positivity
    have hx:0≤z:=by unfold z; positivity
    have hA:0≤A:=by unfold A; positivity
    let X:ℝ:= Real.exp u*z^u * P^m; let Y := ∑ p∈U, Q p*A; have hX:0≤X:=by unfold X; positivity
    have hY:0≤Y:=Finset.sum_nonneg (fun v _=> mul_nonneg (hQ v) hA)
    refine ⟨max A (X+Y),hA.trans (le_max_left ..),fun L ho S h x t w a=>?_⟩
    let V:= candor S x.1 t; let W:=size w; let o:=piz L x a; let l:ℝ:=L.val
    have hl : 1≤l:= Nat.one_le_cast.mpr L.pos; have hl':0<l:=zero_lt_one.trans_le hl
    let s (u:ℕ):= (1+(W:ℝ))^u; have hr(i):0≤ s i:=by unfold s; positivity
    by_cases hw:size w≤ L.val
    · have hR : Knoxville (grain (fame _) 1) u o (partD S x.1 t d w) ((W:ℝ)^d*(A*l⁻¹^(m+d))):= by
         apply climb_sharp _ (by positivity) d w; intro v hv x' hy; have hb:= gala_local hs hc u S d h ho x t x' a (hy.trans hw) v hv.le; rw [hv] at hb;exact hb
      apply hR.mono; change _ ≤ _*s u * _; rw [←mul_assoc,mul_comm _ A]; refine mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left ..) ?_ (by positivity) (hA.trans (le_max_left ..))) (by positivity)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg W) (le_add_of_nonneg_left zero_le_one) _).trans (natpow _ _ hd _ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    have hk:L.val≤ W:= Nat.le_of_lt (Nat.lt_of_not_ge hw); have hh:=unhatched hs hc u S d h x t w a
    have hz :1 ≤ (W:ℝ)/l := (one_le_div hl').mpr (Nat.cast_le.mpr hk); have hu:1+(W:ℝ)≥1:= le_add_of_nonneg_right (Nat.cast_nonneg _)
    let c:ℝ:= (1+(W:ℝ))*l⁻¹; have he: W/l≤ c := by unfold c;rw [div_eq_mul_inv]; gcongr; linarith
    have he':1 ≤ c:= hz.trans he
    have hb : Knoxville (grain (fame _) 1) u o (V w) (X * s u * l⁻¹^(m+d)):= by
       apply hh.mono
       have H:1+(m:ℝ)*((W:ℝ)/l+8) ≤ z*c:= by unfold z; nlinarith only [hz,he',he, mul_nonneg (show 0≤(m:ℝ) by positivity) (show 0 ≤ 9*c-(W/l+8) by linarith)]
       have hj:(1+(m:ℝ)*((W:ℝ)/l+8))^u ≤ z^u*s u*l⁻¹^d:= by
          calc
             _ ≤ (z*c)^u:=pow_le_pow_left₀ (by positivity) H _
             _ = z^u*s u*l⁻¹^u := by unfold c s; rw [mul_pow,mul_pow,mul_assoc]
             _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (inv_nonneg.mpr hl'.le) (inv_le_one_of_one_le₀ hl) hd) (by positivity)
       have hh : sack u η*(Fintype.card J*(C*l⁻¹))=P*l⁻¹:= by unfold P; ring
       change Real.exp (u:ℝ) * (1+(m:ℝ)*((W:ℝ)/l+8))^u * (sack u η*(Fintype.card J*(C*l⁻¹)))^m ≤ _; rw [hh]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le) (by positivity)).trans_eq ?_; unfold X; rw [pow_add,mul_pow];ring
    have hm (p)(hp:p∈U) : Knoxville (grain (fame _) 1) u o (Chapel.hat p w • gang V (roll p) 0) ((Q p*A)*s u*l⁻¹^(m+d)):= by
       have hg : upper p ≤ d:= ((trim_def ..).mp hp).le
       have ho:= (gala_local hs hc u S d h ho x t 0 a (show size (0:cloud m)≤_ by simp [size]) (roll p) (by rw [merch]; exact hg)).smul (Chapel.hat p w); rw [merch] at ho
       apply ho.mono; change _*(A*l⁻¹^(m+upper p)) ≤ _; apply (mul_le_mul_of_nonneg_right (HQ p w) (show 0≤ A*l⁻¹^(m+upper p) by positivity)).trans; have he := (natpow _ _ hg c he'); unfold c at he;rw [mul_pow,mul_pow] at he
       have H : s (upper p)*l⁻¹^upper p ≤ s u*l⁻¹^d:= he.trans (mul_le_mul_of_nonneg_right (natpow _ _ hd _ hu) (by positivity)); change Q p * s _ * _ ≤ _;rw [pow_add,pow_add];calc
           _ = Q p*A * l⁻¹^m * (s _ * l⁻¹^upper p):= by ring
           _ ≤ Q p*A*l⁻¹^m*(s u*l⁻¹^d):= mul_le_mul_of_nonneg_left H (mul_nonneg (mul_nonneg (hQ p) hA) (by positivity))
           _ = _:= by ring
    have hf : Knoxville (grain (fame _) 1) u o (party d V w) (Y*s u*l⁻¹^(m+d)):= by unfold Y party U; rw [Finset.sum_mul,Finset.sum_mul]; exact knox_sum _ (fun i hi=>hm i hi)
    apply (penn_sub hb hf).mono; rw [← add_mul,←add_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (hr u)) (by positivity)
omit [Fintype I] in
lemma hike (x:Biglot I)(t:chain I m)(u:ℕ)(T:Tile (Biglot I) (m+1))(hp:Bail (grain (fame I) 1) u T C):
    (∑' w:cloud m, ENNReal.ofReal ((1+(size w:ℝ))^u) * ‖rowC T x t w‖ₑ) ≤ ENNReal.ofReal ((1+(m:ℝ))^u*C):= by
   let f : cloud m → pack (0:Fin (m+1)) x := fun w=>⟨Fin.cons x (snake x.1 t w),by simp⟩
   have hf : Injective f:= fun u v e=> reptile x.1 t (show _ from by simpa only [f,Fin.cons_inj,true_and] using! congr_arg Subtype.val e)
   let P:ℝ:=(1+(m:ℝ))^u; have hP:0≤P:=by unfold P; positivity
   rw [ENNReal.ofReal_mul hP]; refine le_trans ?_ (mul_le_mul_right (hp.watch f hf) _); rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; rw [glitter,←mul_assoc,plume,Gorge.shine,←ENNReal.ofReal_mul hP]; apply mul_le_mul_left; apply ENNReal.ofReal_le_ofReal
   let w:= wide (fame _) (f v).val
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (grain_down u w) hP); simp only [P,_root_.YM.FormalBulk08.Sable.gauge,NNReal.coe_one,one_mul,←mul_pow]; apply pow_le_pow_left₀ (by positivity); have he:(size v:ℝ)≤ (m:ℝ)* w:= by exact_mod_cast serp x t v
   linarith [show 0 ≤ (m:ℝ) by positivity, show 0≤ (w:ℝ) by positivity]
end YM.FormalBulk08.Sable
