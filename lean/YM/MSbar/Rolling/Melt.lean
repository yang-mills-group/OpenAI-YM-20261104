import YM.MSbar.Rolling.Stove
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Next.SectorChange Further.GaussianScalar
open Push Push.Uniform RG Wilson Gauge Lattice Tree Precision Metric Exterior Price
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c f:Side}{S: StepData c f}(B: Forest S.ratio)(i:S.Choices)(R T:PathData G)(p q:Clip)(ρ:fieldDir G c 1→ AxisChart G B)
open Cacao Bakery Portal
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=> PowerSeries.coeff
local notation "X"=> Positions (Primary c G)
local notation "N"=> Positions (Primary f G)
local notation "Y"=> Positions (Key B G)
local notation "Z"=> Positions (Joint B G)
local notation "V"=> Config G f
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "ν"=> center B ρ
variable (J:ChartRatio G)(hJ:LocalRatio J)
variable (n m:ℕ)(A:PowerSeries (Pot (Primary f G))) (F:ℝ → Config G f→ℝ) (u:ℕ)
variable (hc:Serves S G) (hp:Critical B p R ρ) (hq:ClassicalMatch B p q R T ρ)
variable (ht:Trend F A R p u)
noncomputable def boxS (S:StepData c f)(F:ℝ → Config G f→ℝ)(t:ℝ) : Config G c→ℝ:= hutfee S (t⁻¹^2) (F t)
noncomputable def grainS (t:ℝ)(v:Positions (Primary c G)) := Real.exp (height c q T v)*boxS S F t (postcard G c t v)/(t^Fintype.card (Key B G)*exitS (Push.Uniform.block (priced B i p R) 0) J)
variable (hK : Matrix.PosDef (Push.Uniform.block (priced B i p R) 0))
lemma payY (E:Type)(n:ℕ)[NormedAddCommGroup E]:Price (yard n) 0 (fun t x=>(x:E)):=⟨n, Eventually.of_forall (fun x y hy=> (show ‖y‖≤_ from hy).trans_eq (by ring))⟩
include hc hp hq ht hJ hK
lemma thickets : let P:=song B i R p J A ρ
    Price (yard n) (u+1) (fun x y=>grainS B i R T p q J F x y -taste u (picture y (Spring P)) x):=by
    intro P; have hb:=pierce B i R T p q ρ hc.branches ht.quiet hp hq; let H:=height c q T; let a:=exitS K J; have ha:=perk J hJ K hK
    let W:= (tint G (Body 1 c)).toContinuousLinearMap
    have hH : Price (yard n) 0 (fun t (x:Positions (Primary c G))=>H x):=(volley _ (payY X n) (potter (main c q T ∘ W) 2)).egress (Eventually.of_forall (fun x v ht=> by change MvPolynomial.eval _ _ = height _ _ _ _; rw [pots, Premier.second (hb.line W) v, height,hb.second,hb.carriage];rfl))
    obtain ⟨D,hD⟩:= hH; let L:=max (max 1 n) D; let d:= Fintype.card (Key B G); let g:= grainS B i R T p q J F; obtain ⟨u',X',hc',hh⟩:=ht.control; let I(x):= Rolling.fuel x^(L+1)
    let k:=u'+d+(u+1); have hl1: 1≤L:= (le_max_left ..).trans (le_max_left ..); have H₀:n≤ L:= (le_max_right ..).trans (le_max_left ..)
    have hx':Price (yard n) (u+1) (fun t v=> g t v-vital B i R T p q J F t v (L+1)):=by
        obtain ⟨V',hv⟩:= Heath.vocals G; apply fixed 0 (a⁻¹)
        filter_upwards [ht.base,width,exteriorR V' B X' hc hc' hv n L H₀,hD,hh,road D k L (by omega) (lt_of_le_of_lt (le_max_right .. : D≤L) (by omega))] with t hs ⟨hx,h1,hd⟩ hG hr hw hV v hY
        let f':B.Slice G→ℝ:= measureK B F t v; let x:=I t; let S':= urn (ι:=B.Free) (G:=G) x t; let r:=Real.exp (H v); have he: Integrable f' (B.order G) := by
             have hx:= hutEnv (b:=t⁻¹^2) (F t) hc hs.1 (postcard G c t v); exact (RG.Envelope.integrable (f:=f') ⟨hx.meas.comp (Tree.Forest.continuous_drape B).measurable,hx.cost.choose,fun i=>hx.cost.choose_spec (B.drape i)⟩ _)
        have hy:MeasurableSet S' := by
             have hm : Continuous (kerf t (G:=G) (ι:=B.Free)):= (release_continuous ..).comp ((tint G _).continuous.comp (show Continuous (fun x:Y=>t•x) from by fun_prop))
             exact ((isCompact_closedBall ..).image hm).measurableSet
        have hp :boxS S F t (postcard G c t v)=∫ i,f' i∂ B.order G:= hut_rep _ hc hs.1 B _
        let V'':= vital B i R T p q J F t v (L+1); let j:= t^d*a
        have hk: g t v - vital B i R T p q J F t v (L+1)= (∫ y in S'ᶜ,r*f' y∂ B.order G)/j:=by
              unfold g grainS; rw [hp,← integral_add_compl hy he]; rw [integral_const_mul]; unfold vital; change r*(_+_)/j-r*_/j=r*_/j; rw [mul_add, add_div,add_sub_cancel_left]
        have ht : 0< j := mul_pos (pow_pos hx _) ha
        rw [hk,norm_div,Real.norm_of_nonneg ht.le,div_le_iff₀ ht]; apply le_trans (norm_integral_le_integral_norm ..) _; apply le_trans (setIntegral_mono_on (he.const_mul r|>.norm.integrableOn) (integrableOn_const (by simp)) hy.compl (g:=fun _=> t^k) ?_) _
        · intro U hy; have he':0 ≤ f' U:= (hutAlive _ hc hs.1 _ _).le; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _|>.le),Real.norm_of_nonneg he']; let Y':=postcard G c t v; let Q := -(Rolling.fuel t)^(2*L); have hw': f' U≤ Real.exp Q/t^u':= by
              apply husk (F t) hc hs.1 hc' hx hw Y'; intro i hi;  -- remove
              have h' := pow_le_pow_left₀ (mul_nonneg hx.le (pow_nonneg (zero_le_one.trans hd) _)) (hG v (U) i hY hy hi) 2; unfold Q; rw [div_le_iff₀ (pow_pos hx _)]; rw [mul_pow,← pow_mul] at h'; unfold CoverQ at h'; rw [Nat.mul_comm L 2] at h'; linarith only [h']
          apply le_trans (mul_le_mul_of_nonneg_left hw' (Real.exp_pos _|>.le)); rw [←mul_div_assoc,← Real.exp_add]; apply le_trans _ hV
          exact div_le_div₀ (Real.exp_pos _|>.le) (Real.exp_monotone (by have hi:= hr v hY; rw [pow_zero, one_mul] at hi; exact add_le_add_left ((le_abs_self _).trans hi) Q)) (pow_pos hx k) (pow_le_pow_of_le_one hx.le h1 (by unfold k; omega))
        rw [setIntegral_const,smul_eq_mul]; apply (mul_le_of_le_one_left (pow_nonneg hx.le k) ((measureReal_mono (Set.subset_univ _) (by simp)).trans_eq (probReal_univ))).trans -- lemma
        unfold j; rw [pow_zero,mul_one]; suffices ht: (a⁻¹)*(t^(u+1))*(t^d*a)=t^(u+1+d) by rw [ht]; exact pow_le_pow_of_le_one hx.le h1 (by unfold k;omega)
        have hx:0<a:=ha; rw [pow_add]; field_simp;ring
    exact (hx'.nsum (tavern B i R T p q ρ J hJ n (L+1) A F u hc hp hq ht hK (by omega) (by omega))).egress (Eventually.of_forall fun t x _=> by unfold g; unfold P; ring)
end YM.MSbar.Rolling
