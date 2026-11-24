import YM.AveragedStep.Moments.Cargo
import YM.Work.E04
/-! Distance-weighted budgets, under the *actual* one-step law at the
upper β. Even seam/winding bonds in this gauge lift are included here.
Main analytic step will consume these in convolution with the pinned L²
inverse (before integrating/removing the remaining coarse regulator).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG Loops
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section Numbers
variable {n:Side}
def plume (a:ℝ)(x y:Site n):ℝ:=Real.exp (a*(separation x y:ℝ))
lemma plume_pos (a:ℝ)(x y:Site n): 0 < plume a x y:=Real.exp_pos _
lemma plume_mul {a:ℝ}(ha:0≤a)(x y z:Site n):plume a x z ≤ plume a x y*plume a y z:=by
 unfold plume; rw [← Real.exp_add, ← mul_add]; gcongr; exact_mod_cast separation_triangle ..
lemma plume_ge {a:ℝ}(ha:0≤a)(x y:Site n):1 ≤ plume a x y:=Real.one_le_exp (by positivity)
lemma cost_plume (a:ℝ)(ha:0<a)(k:ℕ):∃ C:ℝ,0≤C∧∀ (y:ℝ),0≤y → (8*y+5)^k ≤ C*Real.exp (a*y):=by
 by_cases h:k=0
 · subst k; exact ⟨1,zero_le_one,fun y hy=> by rw [one_mul,pow_zero]; exact Real.one_le_exp (by positivity)⟩
 have hk:0<(k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero h
 let K:=5+8*k/a
 refine ⟨K^k,by unfold K; positivity,fun y hy=>?_⟩
 have ht:8*y+5 ≤ K*Real.exp (a*y/k):=by
   have hh:=Real.add_one_le_exp (a*y/k)
   have he:=Real.one_le_exp (by positivity:0≤a*y/k)
   have ho:0≤8*(k:ℝ)/a := by positivity
   have hf:(8*k/a)*(a*y/k)=8*y:=by field_simp -- k variable casting inference
   unfold K; nlinarith
 apply (pow_le_pow_left₀ (by positivity) ht k).trans_eq
 rw [mul_pow, ← Real.exp_nat_mul]; field_simp [hk.ne']
lemma seam_price (a:ℝ)(ha:0<a)(d:ℕ):∀ᶠ τ:ℝ in atTop,∀ (c:Side) (x y:Site c),
    (Real.log τ)^2 ≤ (c.val:ℝ) → ¬Loops.Nearest x y→ τ^d ≤ plume a x y:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (8*(d:ℝ)/a+8)] with τ ht he c x y h hh
 let t:ℝ:= Real.log τ
 let s:ℝ:= separation x y
 have hp : t^2 ≤ 4*(s+1) := h.trans (by
   have hw: c.val≤4*(separation x y+1):=le_of_not_gt hh
   unfold s; exact_mod_cast hw)
 have hd:= Nat.cast_nonneg (α:=ℝ) d
 have hx : 8≤t := le_trans (by linarith only [show 0 ≤ 8*(d:ℝ)/a by positivity]) he
 have hs: 1≤s:=by nlinarith
 conv_lhs=> arg 1; rw [← Real.exp_log ht]
 rw [←Real.exp_nat_mul]; apply Real.exp_monotone
 change (d:ℝ)*t ≤ a*s
 change 8*(d:ℝ)/a+8≤t at he
 have hf: 8*(d:ℝ) ≤ t*a := by apply (div_le_iff₀ ha).mp; linarith
 nlinarith only [hx,hs,hf,mul_nonneg (show 0 ≤ t*a-8*(d:ℝ) by linarith only [hf]) (show 0≤t from by linarith only [hx]), mul_le_mul_of_nonneg_left hp ha.le, show 4*a*(s+1)≤8*s*a from by nlinarith]
end Numbers
variable {G:Gauge}{c f:Side}
def breeze (S:StepData c f)(τ:ℝ)(x:Site c)(e:Edge (Site c)):Query S G:=fun _ U=>τ*G.chord (Loops.setGauge x U.2 e)
lemma breeze_safe {τ:ℝ}{x:Site c}{e}{S:StepData c f} : Admits (breeze (G:=G) S τ x e):= fun _=> env_continuous (by unfold breeze; unfold Loops.setGauge Lattice.gauge; fun_prop)
lemma breeze_paid (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(d:ℕ)(a:ℝ)(ha:0<a) : ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ τ:ℝ in atTop,∀ {c f:Side}(S:StepData c f),S.patch=P→ S.kernel=K→4∣f.val → (Real.log τ)^2 ≤ (c.val:ℝ) → ∀ (x:Site c)(e:Edge (Site c)),Ranked τ (breeze S (G:=G) τ x e) d (B* lag τ^d * plume a x e.1) := by
 by_cases hd:d=0
 · subst d; refine ⟨1,zero_le_one,Eventually.of_forall ?_⟩; intro τ c f S hS hK _ _ x e
   exact (Ranked.zero (by rw [hS,hK]; exact h:S.patch.Branches S.kernel G) breeze_safe).enlarge (by simpa using plume_ge ha.le x e.1)
 obtain ⟨C,hC,H⟩:=cargo_price G P K h d
 obtain ⟨D,hD,Hd⟩:=cost_plume a ha (2*(d+1))
 let B:=max (C*D) ((2:ℝ)^d)
 refine ⟨B,by unfold B; positivity,?_⟩
 filter_upwards [H,seam_price a ha d,eventually_ge_atTop (1:ℝ)] with τ H hSeam ht
 intro c f S hS hK hF hP x e
 have hs : S.patch.Branches S.kernel G:=by rw [hS,hK]; exact h
 by_cases he : Loops.Nearest x e.1
 · obtain ⟨l,hl,HL⟩:= Loops.gauge_list x e he
   let s:ℕ:=separation x e.1
   have hh:=ranked_list hs hd l (cargo (G:=G) S τ) (C*lag τ^d) (fun i=>H c f S hS hK hF i)
   refine Ranked.enlarge (C:=(l.length:ℝ)^d*((l.length:ℝ)*(C*lag τ^d))) ?_ ?_
   · apply Ranked.below hs breeze_safe hh; intro i U _
     change |τ*G.chord (Loops.setGauge x U.2 e)| ≤ _
     rw [abs_of_nonneg (by positivity [G.chord_nonneg (Loops.setGauge x U.2 e)]: 0≤ τ*G.chord (Loops.setGauge x U.2 e))]
     apply le_trans _ (le_abs_self _)
     simpa only [cargo,scaled_bill,List.map_map] using (mul_le_mul_of_nonneg_left (HL G U.2) (zero_le_one.trans ht))
   have ho: (l.length:ℝ)≤(8*(s:ℝ)+5)^2:=by exact_mod_cast hl
   let t:ℝ:=8*(s:ℝ)+5
   have hk:(l.length:ℝ)^(d+1) ≤ D*plume a x e.1:=by refine (pow_le_pow_left₀ (by positivity) ho (d+1)).trans ?_; rw [← pow_mul]; exact Hd s (by positivity)
   have h0:1≤lag τ := lag_ge ht
   rw [show (l.length:ℝ)^d*((l.length:ℝ)* (C*lag τ^d))=(C*lag τ^d)*(l.length:ℝ)^(d+1) from by rw [pow_succ]; ring]
   calc
     _ ≤ C*lag τ^d*(D*plume a x e.1):=by gcongr
     _ ≤ _:= by rw [show C*lag τ^d*(D*plume a x e.1)= C*D*lag τ^d*plume a x e.1 from by ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) (plume_pos ..).le
 have h0:0≤τ:=zero_le_one.trans ht
 apply Ranked.enlarge (C:= |τ*2|^d)
 · apply Ranked.below hs breeze_safe (Ranked.const hs _); intro i u _
   simp only [breeze]; rw [abs_of_nonneg (mul_nonneg h0 (G.chord_nonneg _)),abs_of_nonneg (mul_nonneg h0 zero_le_two)]
   exact mul_le_mul_of_nonneg_left (G.chord_le_two _) h0
 rw [abs_of_nonneg (by positivity),mul_comm τ,mul_pow]
 exact (mul_le_mul_of_nonneg_left (hSeam c x e.1 hP he) (by positivity)).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_mul_of_one_le_right (a:=B) (by unfold B; positivity) (one_le_pow₀ (lag_ge ht)))) (plume_pos ..).le)
end YM.AveragedStep
