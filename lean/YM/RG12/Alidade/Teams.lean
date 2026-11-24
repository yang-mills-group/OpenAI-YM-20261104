import YM.RG12.Frames.Tests
import YM.RG12.Alidade.Chrono
/-! # Full and cut tariff. Includes dilation, both directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Filter Lattice Wilson RG Real Frames Finset
open scoped Topology BigOperators Classical

variable {d:ℕ}{V:Grade d→ Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][FiniteDimensional ℂ (Col V)]
abbrev MC (V:Grade d→Type)[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]:=Col V≃ₗ[ℂ] Col V
variable {F:Type}[AddCommGroup F][Module ℂ F]
private def expand (u:ℝ)(hu:0 < u): MC V:=
    LinearEquiv.ofLinear (dilate u) (dilate u⁻¹) (by apply LinearMap.ext; intro x;exact scale_cancel' hu.ne' x) (by apply LinearMap.ext; intro x; exact scale_cancel hu.ne' x)
def pace (Y X:Col V≃ₗ[ℂ] F)(u:ℝ)(hu:0 < u):MC V:= (expand u hu).trans (X.trans Y.symm)
set_option linter.unusedSectionVars false
lemma pace_at (Y X:Col V≃ₗ[ℂ] F){u:ℝ}(hu:0 < u)(x:Col V):pace Y X u hu x=Y.symm (X (dilate u x)):=rfl
lemma pace_symm (Y X:Col V≃ₗ[ℂ] F){u:ℝ}(hu:0 < u)(x:Col V):(pace Y X u hu).symm x=dilate u⁻¹ (X.symm (Y x)):=rfl
lemma pace_pull (Y X:Col V≃ₗ[ℂ] F){u:ℝ}(hu:0 < u)(x:Col V):
    X x= Y ((pace Y X u hu) (dilate u⁻¹ x)):=by rw [pace_at,scale_cancel' hu.ne', Y.apply_symm_apply]
lemma pace_back (Y X:Col V≃ₗ[ℂ] F){u:ℝ}(hu:0 < u)(x:F): X.symm x=dilate u ((pace Y X u hu).symm (Y.symm x)):=by rw [pace_symm,Y.apply_symm_apply,scale_cancel' hu.ne']

-- on literature normalized matrices, filtration compatible relative P
abbrev formative (Y P:Col V≃ₗ[ℂ] F): Prop:=triangular V (Y.trans P.symm).toLinearMap
lemma pace_form (Y X:Col V≃ₗ[ℂ] F){P:Col V≃ₗ[ℂ] F}(hY:formative Y P)(hX:formative X P){u:ℝ}(hu:0<u):triangular V (pace Y X u hu).toLinearMap:=by
   have he := (triangular.inv hY).comp (hX.comp (tri_dilate (V:=V) u))
   intro i j hj x; specialize he i j hj x
   change Y.symm (P (P.symm (X _))) i=0 at he; rwa [P.apply_symm_apply] at he

variable {x y:ℝ}{g h:Currency V}{K:ℝ}
-- bridge, *unmoving* s-weight, coarse opnorm ok on triangular block. Exponent through entire matrix unchanged.
omit [FiniteDimensional ℂ (Col V)] in
theorem touched (b:ℕ)(hg:Fits g K)(hh:Fits h K){A: BlockMatrix V}(hc:triangular V A) (U:ℝ)(H:∀ v, ‖A v‖ ≤ U * ‖v‖)(H0:0 ≤ U){s:ℝ}(Hs:1 ≤ s)(v:Col V): coins b g s (A v) ≤ (↑d+1)*K^2*U * coins b h s v:=by
    let t:= fun i:Grade d=>price b i s
    have ht(i):0≤t i:=pow_nonneg (zero_le_one.trans Hs) _
    have hK:=zero_le_one.trans hg.legal
    let B:=K^2*U
    have he(i j:Grade d)(v:V j): t i * g i (block V A i j v) ≤ B*(t j * h j v):=by
      rcases le_or_gt i j with hq|hq
      · have hx: g i (block V A i j v) ≤ B*h j v:=by
           let u:= put V j v
           have hr:= (norm_le_pi_norm (A u) i).trans (H u)
           have hz:= (put_norm_le (V:=V) j v).trans (hh.lower j v)
           calc _ ≤ K * (U*(K*h j v)):= (hg.upper ..).trans (mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_left hz H0)) hK)
                _ = B*h j v:=by unfold B; ring
        calc _ ≤ t j * (B * h j v) := mul_le_mul (pow_le_pow_right₀ Hs (Nat.mul_le_mul_right (b+1) hq)) hx (hg.nonneg ..) (ht j)
             _ = _:=by ring
      rw [hc i j hq v,hg.zero,mul_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg K) H0) (mul_nonneg (ht _) (hh.nonneg ..))
    have hh'(i:Grade d)(J:Finset (Grade d)):g i (∑ j∈J,block V A i j (v j)) ≤ ∑ j∈J, g i (block V A i j (v j)):=by
       induction J using Finset.induction_on with
       | empty=> simp [hg.zero]
       | insert i T hA IH=> rw [sum_insert hA,sum_insert hA]; exact (hg.subadd ..).trans (add_le_add le_rfl IH)
    unfold coins
    calc
       _ ≤ ∑ i:Grade d, ∑ j:Grade d,B* (t j*h j (v j)):=
         sum_le_sum fun i _=>by
           change t i * _ ≤ _
           rw [block_sum]; refine (mul_le_mul_of_nonneg_left (hh' i univ) (ht i)).trans ?_
           rw [mul_sum]; apply sum_le_sum; exact fun j _=>he i j (v j)
       _ = _:=by rw [← mul_sum,sum_const,card_univ]; simp only [nsmul_eq_mul,Grade,B,t,Fintype.card_fin,Nat.cast_add,Nat.cast_one,mul_assoc]

abbrev wallet (Y:ℕ→ℝ)(m:ℕ)(e:ℕ→ℝ)(s:ℕ→ℝ)(i:ℕ):= s i^m * interest e m i * Y i
abbrev pot {G:Gauge}(Z:Levels G)(A Q:ℕ)(e:ℕ→ℝ): ℕ→ℝ:= wallet (outer Z Q) A e (epoch Z)
lemma pot_big {G:Gauge}(Z:Levels G)(A Q i:ℕ){e:ℕ→ℝ}(he:∀ i,0≤e i):1 ≤ pot Z A Q e i:= by
   have hS:= one_le_pow₀ (n:=A) (begun Z i); have hi := interest_big he A i; have hO := outer_big Z Q i
   exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS hi) hO

variable {G:Gauge}{Z:Levels G}{Y X P:Col V ≃ₗ[ℂ] F} {p c D:ℕ}{e:ℕ→ℝ}{K a:ℝ}{i:ℕ}{g₀ g₁:F→ℝ}
local notation "clk"=>epoch Z
-- one-step literal adjacent. any shears tested in local criterion, but they cost s^b already
structure Near (Z:Levels G)(e:ℕ→ℝ)(p c D i:ℕ)(Y X:Col V≃ₗ[ℂ] F)(g₀ g₁:F→ℝ)(K a:ℝ)(ha:0<a) : Prop where
   power: d*(p+c+4+1)+(p+d+1) ≤ D
   tests : ∃ J:MC V, Compared (pace Y X a ha) J (g₀∘Y) (g₁∘X) K (epoch Z i) ((epoch Z (i+1)/epoch Z i)*Real.exp (e i)) p c
lemma pot_forward (h:G.Simple){Q:ℕ}{e:ℕ→ℝ}(_he:∀ i,0≤e i) (A i:ℕ):
     pot Z A Q e i * ((epoch Z (i+1)/epoch Z i)*Real.exp (e i))^A ≤ pot Z A Q e (i+1):=by
    let s:= epoch Z i; have hs: 0 < s:=zero_lt_one.trans_le (begun Z i)
    have ho:= outer_east Z h Q i (i+1) (Nat.le_succ i)
    unfold pot wallet; rw [←interest_next]
    calc _ = epoch Z (i+1)^A * (interest e A i* exp (e i)^A)*outer Z Q i:=by rw [mul_pow,div_pow]; field_simp [pow_ne_zero _ (show epoch Z i ≠ 0 from hs.ne')]
         _ ≤ _ := mul_le_mul_of_nonneg_left ho (mul_nonneg (pow_nonneg (zero_le_one.trans (begun Z _)) _) (mul_nonneg (show 0 ≤ interest e A i from (exp_pos _).le) (pow_nonneg (exp_pos _).le _)))
lemma step_factor_small {e:ℕ→ℝ}(he:∀ i,e i ≤ 1): ∀ᶠ i in atTop, (clk (i+1)/clk i)* Real.exp (e i) ≤ clk i:=by
    filter_upwards [epoch_neighbor Z,(epoch_late Z).eventually_ge_atTop (2*Real.exp 1)] with i h₀ h₁
    exact (mul_le_mul h₀ (Real.exp_monotone (he i)) (exp_pos _).le zero_le_two).trans h₁
lemma near_prices {a:ℝ}{i:ℕ}{hi:0<a}(h:G.Simple)(he:∀ i,0 ≤ e i)(H:Near Z e p c D i Y X g₀ g₁ K a hi) (s: K ≤ epoch Z i) (hm:(clk (i+1)/clk i)*Real.exp (e i) ≤ clk i) (v:Col V)(Q:ℕ): let b:=p+c+4; let f₁:=compress (g₁∘X); let f₀:=compress (g₀∘Y); let A:=pace Y X a hi; let T:=pot Z D Q e
    T i*coins b f₀ (clk i) (A v) ≤ T (i+1)*coins b f₁ (clk (i+1)) v ∧ T i*coins b f₁ (clk (i+1)) (A.symm v) ≤ T (i+1)*coins b f₀ (clk i) v:=by
   intro b f' f A T
   obtain ⟨J,Hq⟩:=H.tests
   let r:=(clk (i+1)/clk i)*Real.exp (e i);let l:= clk (i+1)/clk i
   have hf:r≥ l:= le_mul_of_one_le_right (zero_le_one.trans (epoch_unit Z (Nat.le_succ i))) (Real.one_le_exp (he i))
   have ha:1+(clk i)⁻¹≤ r:=(epoch_ratio Z (Nat.lt_succ_self i)).trans hf
   have hl:1≤l:=epoch_unit Z (Nat.le_succ i); have hr:=hl.trans hf
   have hx : 0 < clk i:=zero_lt_one.trans_le (begun Z i)
   obtain ⟨hp',hq'⟩:=TestedStep Hq s hr hm
   have hw :0 ≤ T i:=zero_le_one.trans (pot_big Z D Q i he)
   constructor
   · calc _ ≤ T i*(r^D*coins b f' (clk (i+1)) v):= by
            apply mul_le_mul_of_nonneg_left _ hw
            refine (hp'.pay_all (begun Z i) ha v).trans ?_
            have h':(p+(d+1))≤ D:=by have ht:=H.power; omega
            exact mul_le_mul (pow_le_pow_right₀ hr h') (coin_mono hp'.basic_i hx.le (epoch_move Z (Nat.le_succ i)) v) (coins_nonneg hp'.basic_i hx.le _) (zero_le_one.trans (one_le_pow₀ hr))
          _ ≤ _:=by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (pot_forward h he _ _) (coins_nonneg hp'.basic_i (zero_le_one.trans (begun Z _)) _)
   calc
     _ ≤ T i*(l^(d*(b+1)) * coins b f' (clk i) (A.symm v)):=
        mul_le_mul_of_nonneg_left (enlarge hq'.basic_o (begun Z i) hl (div_mul_cancel₀ _ hx.ne').symm (A.symm v)) hw
     _ ≤ T i*(r^(d*(b+1)) * (r^(p+(d+1)) * coins b f (clk i) v)):=mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hl) hf _) (hq'.pay_all (begun Z i) ha v) (coins_nonneg hq'.basic_o hx.le _) (pow_nonneg (zero_le_one.trans hr) _)) hw
     _ ≤ _:=by
        have hv:=coins_nonneg (b:=b) hq'.basic_i hx.le v
        rw [←mul_assoc (r^_),←pow_add,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hv
        have ht:d*(b+1)+(p+(d+1)) ≤ D:=by have h₀ := H.power; unfold b; omega
        exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr ht) hw).trans (pot_forward h he D i)
-- no credit for lit comparisons required on cross edges. pays *fixed* power on full connector before coin convert
lemma pot_angle (h:G.Simple){Q:ℕ}{e:ℕ→ℝ}(he:∀ i,0≤e i) (A i j m:ℕ)(hA:i ≤ j)(hV:Z.clock.J i < m)(hM:m ≤ Z.clock.J j):
    pot Z A Q e i * (((epoch Z j/epoch Z i)^A)*radar (Z.clock.hatBeta j) m^Q) ≤ pot Z A Q e j:=by
    have hs:0 < epoch Z i:=zero_lt_one.trans_le (begun Z i)
    have hp := outer_step Z h Q i j m hA hV hM
    unfold pot wallet
    have ht:0 ≤ clk j^A:=pow_nonneg (zero_le_one.trans (begun Z _)) _
    calc _ = clk j^A * interest e A i*(outer Z Q i*radar (Z.clock.hatBeta j) m^Q):=by rw [div_pow]; field_simp
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (interest_mono he A hA) ht) hp (by have h₀:=year Z j; exact mul_nonneg (zero_le_one.trans (outer_big Z Q _)) (pow_nonneg (exp_pos _).le _)) (mul_nonneg ht (zero_le_one.trans (interest_big he ..)))
omit [FiniteDimensional ℂ (Col V)] in
lemma bridge_prices {i j m a b:ℕ}{g h:Currency V}(hs:G.Simple)(he:∀ i,0≤e i)(hg:Fits g K)(hh:Fits h K){A:MC V}
    (hu:triangular V A.toLinearMap)(hv:triangular V A.symm.toLinearMap)(hj:i≤j)(hm:Z.clock.J i < m)(hz:m ≤ Z.clock.J j)
    (hW: let W:=radar (Z.clock.hatBeta j) m; ∀ v,‖A v‖ ≤ W^a*‖v‖ ∧ ‖A.symm v‖ ≤ W^a*‖v‖)
    (hQ:((d:ℝ)+1)*K^2 ≤ radar (Z.clock.hatBeta j) m)(H:d*(b+1) ≤ D)(v:Col V): let T:=pot Z D (1+a) e
    T i*coins b g (clk i) (A v) ≤ T j*coins b h (clk j) v ∧ T i*coins b h (clk j) (A.symm v) ≤ T j*coins b g (clk i) v:=by
   let W:=radar (Z.clock.hatBeta j) m;let r:= clk j/clk i
   intro T
   have hw:1≤W:=radar_big (delay Z j) m; have h':0<(W^a):=pow_pos (zero_lt_one.trans_le hw) a
   have hr:1 ≤ r:=epoch_unit Z hj;have hi: 1 ≤ clk i:=begun Z i
   have hP :0 ≤ T i:=zero_le_one.trans (pot_big Z D (1+a) i he)
   have he':T i*(r^D*W^(1+a)) ≤ T j:=pot_angle hs he D i j m hj hm hz
   have hy {g h:Currency V}(hg:Fits g K)(hh:Fits h K)(A: MC V)(hu:triangular V A.toLinearMap)(ht:∀ v,‖A v‖ ≤ W^a*‖v‖) : coins b g (clk i) (A v) ≤ W^(1+a)*coins b h (clk i) v:=
     (touched b hg hh hu (W^a) ht h'.le hi v).trans (mul_le_mul_of_nonneg_right (by rw [pow_add,pow_one]; gcongr) (coins_nonneg hh (zero_le_one.trans hi) v)) -- hQ
   constructor
   · calc _ ≤ T i*(r^D*W^(1+a))*coins b h (clk j) v :=by
            conv_rhs => rw [mul_assoc (T i)]
            apply mul_le_mul_of_nonneg_left _ hP; refine (hy hg hh A hu (fun w=>(hW w).1)).trans ?_
            exact mul_le_mul (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hw) _) (one_le_pow₀ hr)) (coin_mono hh (zero_le_one.trans hi) (epoch_move Z hj) v) (coins_nonneg hh (zero_le_one.trans hi) v) (mul_nonneg (zero_le_one.trans (one_le_pow₀ hr)) (pow_nonneg (zero_le_one.trans hw) _))
          _ ≤ _ :=mul_le_mul_of_nonneg_right he' (coins_nonneg hh (zero_le_one.trans (begun Z j)) v)
   have he0:clk j =r*clk i:=(div_mul_cancel₀ _ (zero_lt_one.trans_le hi).ne').symm
   have hv' := coins_nonneg (b:=b) hg (zero_le_one.trans hi) v
   calc _ ≤ T i*(r^(d*(b+1))*coins b h (clk i) (A.symm v)) := mul_le_mul_of_nonneg_left (enlarge hh hi hr he0 _) hP
        _ ≤ T i*(r^D*(W^(1+a)*coins b g (clk i) v)):= mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hr H) (hy hh hg A.symm hv (fun v=>(hW v).2)) (coins_nonneg hh (zero_le_one.trans hi) _) (zero_le_one.trans (one_le_pow₀ hr))) hP
        _ ≤ _ :=by rw [← mul_assoc _ (W^(1+a)),← mul_assoc]; exact mul_le_mul_of_nonneg_right he' hv'
end YM.RG12.Alidade
