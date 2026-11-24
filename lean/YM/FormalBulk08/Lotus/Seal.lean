import YM.FormalBulk08.Lotus.Arks

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} [Fintype I] {η : ℝ} {r : ℕ}

omit [Fintype I] in
lemma shore (n : Side) {M : Tor n I→ Tor n J →ℝ} {B C : ℝ} (h : Hill (rinkshine η n) M B C) (x : Tor n I) (y : Biglot J) (hs : 0≤η) :
    ‖M x (drip n y)‖ ≤ (B*Real.exp (η*size y.1))*coast η (boil n x) := by
   let Y:= drip n y
   have ht:= (ENNReal.le_tsum (f:=fun v=>rinkshine η n x v*‖M x v‖ₑ) Y).trans (h.rows x)
   unfold rinkshine shine at ht; rw [←ofReal_norm, ←ENNReal.ofReal_mul (Real.exp_pos _).le] at ht
   let t:=skit n (Y.1-x.1); have he: Real.exp (η*t)* ‖M x (drip n y)‖ ≤ B:= (ENNReal.ofReal_le_ofReal_iff h.costs).mp ht
   have hp : skit n x.1 ≤ t + size y.1 := by
      have hz:= skit_add n (x.1-Y.1) Y.1;rw [sub_add_cancel,skit_sub] at hz; exact hz.trans (Nat.add_le_add_left (skirt ..) _)
   calc
      _ = Real.exp (-(η*t))*(Real.exp (η*t)* ‖M x (drip n y)‖) := by rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
      _ ≤ B*Real.exp (-(η*t)) := by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ ≤ _ := by
         rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h.costs; unfold coast;rw [←Real.exp_add]; apply Real.exp_monotone;change -(η*t)≤ η*(size y.1)+ (-η* skit n x.1);have hy : (skit n x.1:ℝ)≤ (t:ℝ)+size y.1:= by exact_mod_cast hp
         nlinarith

lemma monsoon (h : 0<η) : Summable (fun v : chain (Biglot I) r => ∏ i,coast η (v i)) := by
   refine ENNReal.summable_toReal (f:=fun v=> ∏ i, ENNReal.ofReal (coast η (v i))) ?_ |>.congr ?_
   · rw [eun_tsum (fun (_:Fin r) v=> ENNReal.ofReal (coast η (v : Biglot I)))]; simp only [ne_eq]; apply ENNReal.prod_ne_top; intro i _; exact (coast_sum h).tsum_ofReal_ne_top
   intro v; simp_rw [ENNReal.toReal_prod]; congr 1; ext i; unfold coast; rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma sparkle_pearl {q : Biglot I → Biglot J→ℝ} {M : (n:Side)→ Tor n I→Tor n J→ℝ}
    {T : Tile (Biglot I) r} {P : (n:Side)→Tile (Tor n I) r} (h : Light T P) (H : Wind q M) (b c a : ℝ) (hs : 0<η) (hx : Bright P η a) (hr : ∀ᶠ n in atTop, Hill (rinkshine η n) (M n) b c) (i : Fin r) :
    Light (pearl q T) (fun n=>pearl (M n) (P n)) := by
   intro v; let Y n (u : chain (Tor n I) r) := P n u * ∏ j, M n (u j) (drip n (v j))
   let C (j:Fin r) := b*Real.exp (η*size (v j).1)
   obtain ⟨l,ht,hu⟩:=(hx.and hr).exists; have ha:=ht.1; have hc (j:Fin r):0≤C j := mul_nonneg hu.costs (Real.exp_pos _).le
   refine jolt_limit (glaze I r) Y (fun w=> T w*∏ j,q (w j) (v j)) (fun w=> (a*∏ j,C j) * ∏ j,coast η (w j)) ((monsoon hs).mul_left _) (fun j=>mul_nonneg (mul_nonneg ha (Finset.prod_nonneg fun i _=>hc i)) (Finset.prod_nonneg fun i _=>(Real.exp_pos _).le)) (fun w=> Tendsto.mul (h w) (tendsto_finsetProd _ fun j _=> H (w j) (v j))) ?_
   filter_upwards [hx,hr] with n hn hk w; unfold Y;rw [norm_mul,norm_prod,mul_assoc,←Finset.prod_mul_distrib]; exact mul_le_mul (hn.value hs.le w i) (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>shore n hk _ _ hs.le)) (Finset.prod_nonneg fun _ _=> norm_nonneg _) ha
end YM.FormalBulk08.Lotus
