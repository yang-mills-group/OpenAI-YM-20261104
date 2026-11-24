import YM.RG01Estimate.Palisade
/-!
 # Sufficient post-Block wages for unmarked tray purchase. Funding all
 analytic Loyalty charges, independent of auxiliary choice. explicit eta
 absorbing gate, to be used before activation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Precise
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard Award
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio
open Progress.DirectedRecipe Next.Scheduling
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}
   {N m d n i j r ℓ:ℕ}
variable {C:Targets X.p X.K}{Z:Expenses C}{p: Return.Wages}{v:ℕ→ℝ}(R:PhysicalNext.Repeat.Register D Z p v)
    (h:4 ≤ j)(he:StepStages j i)
local notation "I₀" => X.p.profile i
local notation "J₀" => X.p.profile j
local notation "L" => (D.L j)
variable (H : Horizon X D j i ℓ r n h){Qp: Postage}(T: Time.Forecast Qp)
   {s a b d':ℝ→ℝ}
lemma income {e:ℕ}(f:Folio D h H e s a b d') (ha:Cookie G (D.L j) a) (hb:Cookie G (D.L j) b) (hd:Cookie G (D.L j) d') : Cookie G (D.L j) (Precise.wage D h H f):= by
    have hM: Cookie G L (capΨ D h H a):= Promise.view_cost (fun i=>Trio.paySide G L ℓ i) H.Y (fun _=>cloak D j) a (Cookie.bolt (Trio.circles ..)) H.Y' (Cookie.const _) ha _ _
    have hx:Cookie G L (pot d'):= (Cookie.const _).joins hd
    have hz: Cookie G L (sFee D h H f):= Award.stake_estate _ _ _ f.K' hM hb H.hl hx
    exact hx.joins ((Cookie.const _).pays hz)
-- explicit subpower spending for ANY fixed requested loss on gate. Need iteration.
lemma priced {f:ℝ→ℝ}(t:ℝ)(ht:0<t)(hp:Cookie G (D.L j) f) (r:ℕ): ∀ᶠ x in atTop,∀ β:ℝ,betaF G x (D.L j)/2≤β→β≤2*betaF G x (D.L j)→ gStep β^(r+1)*f x ≤ gStep β ^ ((r:ℝ)+1-t):= by
   have hy:Rate G L (t/2) (fun x=> gStep (betaF G x L)^(-t)):= by
      apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; unfold gStep; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ←Real.rpow_mul hx.le]; congr 1; ring
   let w x:= betaF G x L; let v x:=gStep (w x)
   have ht₀: Rate G L (-(t/2)) (fun x=> v x^t) := by
      apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; unfold v w gStep; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ←Real.rpow_mul hx.le]; congr 1; ring
   filter_upwards [Delay.shift_pos G L, (ht₀.mul hp.uses|>.mul_left ((2:ℝ)^t)).below (by linarith) 1 zero_lt_one] with x hx hi β hB _
   have h' := (lamp G L hx β hB); let p:=gStep β; have hh:p^(t)≤ (2:ℝ)^t *v x^t:= (Real.rpow_le_rpow h'.1.le h'.2 ht.le).trans_eq (Real.mul_rpow zero_le_two (inv_nonneg.mpr (Real.sqrt_nonneg _)))
   have hv:p^t*f x≤1:= by
      have hp:0≤p^t:=Real.rpow_nonneg h'.1.le _
      by_cases hz:0≤f x
      · refine (mul_le_mul_of_nonneg_right hh hz).trans ?_; rw [mul_assoc]; exact (le_abs_self _).trans hi
      exact (mul_nonpos_of_nonneg_of_nonpos hp (not_le.mp hz).le).trans zero_le_one
   change p^(r+1)*f x ≤ _; rw [Real.rpow_sub h'.1]; push_cast at *
   rw [le_div_iff₀ (Real.rpow_pos_of_pos (x:=p) h'.1 t)]
   rw [Real.rpow_add h'.1, Real.rpow_one,pow_succ, Real.rpow_natCast]; rw [mul_assoc (p^r * p),mul_comm (f x) (gStep β ^ t)]; exact mul_le_of_le_one_right (mul_nonneg (pow_nonneg h'.1.le _) h'.1.le) hv
lemma bracing (H:Horizon X D j i ℓ r n h) (e:ℕ)(f:Folio D h H e s a b d') (hy: (Z j i).wanting ≤ -(1/4:ℝ))
    (hs:Cookie G (D.L j) s)(ht: ∀ᶠ t in atTop,Boardwise D R h H f t): ∀ᶠ t in atTop,OpenAt D R h H f T t:= by
   let u:= I₀
   have hp : Rate G L (-(1/4)) (fun t=> sideFee D R i j t + Precise.tiny G L t):= Rate.add ((((Rate.power.weaken hy).add (Rate.power.weaken (show -(7/16:ℝ)≤-(1/4) by norm_num))).mul_left _)) Rate.power
   have hb : Rate G L (-(1/2)) (breath G L):=(glim G L).mul_left 2
   filter_upwards [ht,H.port, Award.steam ℓ u _ (by norm_num : -(1/4:ℝ)< -(1/8:ℝ)) hp, Marlin.pricingBuy G L _ T, (hs.uses.mul hb).below (by norm_num) 1 zero_lt_one, Delay.shift_pos G L,
       affix_cost G L ℓ, Laplace.funding (w:=H.lan) r H.y H.hl.uses H.Y'.uses, (hb.mul H.Y'.uses).below (by norm_num) 1 zero_lt_one, eventually_ge_atTop (Real.exp 1), Precise.spill_rate (r:=r) G L]
     with t ht hP hp hk hs hv hm hK hS hQ hκ
   refine ⟨ht,?_,⟨(le_abs_self _).trans hs,hP.1,hP.2.1⟩,hm,hP.2.2,fun β he hβ=> ?_⟩
   · intro β hB M hR hB' a₀ η Φ D' sf X hQ hx v' hs hx' hv
     rw [hB']; exact hk β hB _ _ hs hv hx' (hp M sf η β Φ D' (r+1) X hQ (fun i=> (hx i).trans hQ) hR)
   exact ⟨(half_pos hv).trans_le he,hv,hQ,hK.2.2.2.2 β he,(le_abs_self _).trans hS,hK.2.2.1,hκ β he hβ⟩

include he
-- can buy any acceptable stipulations after H chosen. Fit into W.Activation before other gates.
lemma horizons (hn: r+1+(X.p.profile i).order ≤ n) (hy:(Z j i).wanting ≤ -(1/4:ℝ)) : ∃ H:Horizon X D j i ℓ r n h,∀ (e:ℕ)(s a b d':ℝ→ℝ),Cookie G (D.L j) s → Cookie G (D.L j) a → Cookie G (D.L j) b → Cookie G (D.L j) d'→
     ∃ f : Folio D h H e s a b d', Cookie G (D.L j) (Precise.wage D h H f) ∧ ∀ᶠ t in atTop, OpenAt D R h H f T t:= by
   let P:= Mural.sheet X.p D h; have hS:2≤n:= by have hf:6≤ (X.p.profile i).order:=(I₀).order_ge; omega
   obtain ⟨HC⟩:= Uniform.pre_order G (J₀).width (J₀).paths P.J X.p.kernel (n:=n+3) (by omega)
   obtain ⟨d,V,hV,hd,hQ⟩:= Board.billboard R h ℓ HC hS he
   obtain ⟨Y,hY,H,hL⟩:= Precise.opens G L (ℓ:=ℓ)
   let Q:= BareRates.offered G (I₀).width (I₀).paths ((I₀).order+(r+1+2)) |>.some
   obtain ⟨s',hs,Hξ,hK⟩:= lofts G L Y hY (I₀).order
   let G': Horizon X D j i ℓ r n h:= ⟨Q,HC,Y,hY,d,hV,V,hd,s',hs,(hL.and hK).mono (fun t ht=> ⟨H _,Hξ _,ht.1,ht.2⟩)⟩
   refine ⟨G', fun e s a b d' hS hA hn' hF=>?_⟩
   obtain ⟨Ψ,hΨ,J⟩:= Blaze.Brush.compact (f:=Real.exp) (k:=n) (s:=Set.Icc (-1:ℝ) 1) isCompact_Icc (fun x _=> Real.contDiff_exp.contDiffAt)
   have hf:Cookie G L (Precise.amount s n Ψ):= Cookie.lump hS (Cookie.const _) _
   obtain ⟨W,w,B'₀,N',h₁,h₂,h₃,h₄,hT⟩:= hQ (r+1) (X.p.profile i).order (e*n+0) _ Y _ _ 0 hn (by omega) hf hf hY (Rate.const (Real.exp 1))
   let f : Folio D h G' e s a b d':= ⟨Ψ,hΨ.le,J,W,w,B'₀,N',h₁,h₂,h₃,h₄⟩
   exact ⟨f,income h G' f hA hn' hF,bracing R h T G' e f hy hS hT⟩ -- where Τ inference
end YM.RG01Estimate.Precise
