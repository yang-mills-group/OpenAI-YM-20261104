import YM.Contacts.Milling.Hollow
import YM.Contacts.Milling.Wick
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory
open Finset PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form MvPolynomial Radial
open scoped Topology BigOperators ContDiff Classical
noncomputable section
variable {V E : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {ι:Type} [Fintype ι]{L:Law V}{R:ℕ→ Rack ι}
section void
lemma jetConst (n:ℕ)(x:E) : jet (fun _:E=>1) n x= if n=0 then 1 else 0:= by cases n <;> simp [jet,Nat.succ_ne_zero]; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
lemma expand_c {X:PowerSeries (Plate ι)}{f:ℕ→E→ℝ}{x:E}{p:ℕ} (m:ι→ℝ)(i:ℕ)(hp:i≤p)(h:∀ i,i≤p → aeval m (PowerSeries.coeff i X)= f i x):
    aeval m (PowerSeries.coeff i (breath X)) = expsum f i i x := by
  have he (n j:ℕ)(hj:j≤p): aeval m (PowerSeries.coeff j (X^n))=Zone.TaylorPow f n j x:= by
    induction n generalizing j with
    | zero=> by_cases he:j=0<;> simp only [pow_zero, PowerSeries.coeff_one, he,↓reduceIte,map_one,map_zero,Zone.TaylorPow]
    | succ n IH=> rw [pow_succ,PowerSeries.coeff_mul,map_sum]; refine sum_congr rfl fun k hk=> ?_; have H:= mem_antidiagonal.mp hk; rw [map_mul,IH _ (by omega),h _ (by omega)]
  simp only [expsum,breath,expansion,PowerSeries.coeff_mk,map_sum,PowerSeries.coeff_smul,map_smul]; apply sum_congr rfl; intro i hi; rw [he _ _ hp]; rfl
lemma unclad (f:E→ℝ)(n:ℕ)(x:E): integrandSeries f 1 n x= expsum (layers f) n n x := by
    unfold integrandSeries Zone.mul; rw [Finset.sum_eq_single (0,n)]; · rw [jet_zero,Pi.one_apply,one_mul]
    · rintro ⟨i,j⟩ he hi; dsimp only; rw [show jet (1:E→ℝ) i (x) = _ from jetConst i x,if_neg (fun h=> hi <| Prod.ext h (by have H : i+j=n := mem_antidiagonal.mp he; exact show j=n by omega)),zero_mul]
    exact fun e=> (e (mem_antidiagonal.mpr (by simp))).elim
end void
structure Relief (L:Law V)(f:E×V→ℝ)(g:E→ℝ)(y:E→V) : Prop where
    shift x z : jet f 2 (x,y x+z)= jet g 2 x+L.P z z/2
    cont : Continuous y
variable {f:E×V→ℝ}{g:E→ℝ}{m:E→ V}
lemma hilly_ball (h:Relief L f g m)(R:ℝ): ∃ c>0, ∃ C, Hilly f (c+c) R C:= by
    let s:= closedBall (0:E) R; obtain ⟨c,hc,H⟩:=L.slope; obtain ⟨M,Hk⟩:= (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn h.cont.continuousOn
    have hg : Continuous (jet g 2) := by letI:=borel E; apply Smooth.continuousJet
    obtain ⟨D,hD⟩:=(isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hg.continuousOn
    refine ⟨c/4,by positivity,D+c*M^2+c*R^2,fun x hx y=> ?_⟩
    let v:=y-m x
    have hV:m x+v=y:=by unfold v; abel
    have hu :‖y‖ ≤ ‖v‖+ M := by rw [← hV]; exact (norm_add_le ..).trans (by linarith only [Hk _ hx])
    rw [← hV,h.shift,hV, Prod.norm_def]; have hp : c/2*‖y‖^2 ≤ c*‖v‖^2+c*M^2:= by nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) hc.le,mul_nonneg hc.le (sq_nonneg (M-‖v‖))]
    have hh:= neg_le_abs (a:=jet g 2 x)|>.trans (hD x hx); rcases le_total ‖x‖ ‖y‖ with e|e; · rw [max_eq_right e]; nlinarith only [hp,H v,hh,mul_nonneg hc.le (sq_nonneg R)]
    rw [max_eq_left e]; nlinarith only [H v,hh,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hx) 2) hc.le,mul_nonneg hc.le (sq_nonneg M),mul_nonneg hc.le (sq_nonneg ‖x‖),mul_nonneg hc.le (sq_nonneg ‖v‖)]
variable (Y:E→ι→ℝ) (T:ι→Module.Dual ℝ V)
structure Arc (L:Law V)(Y:E→ι→ℝ)(T:ι→Module.Dual ℝ V) (R:ℕ→ Rack ι)(f:E×V→ℝ)(g:E→ℝ)(m:E→V)(n:ℕ)(s:Set E): Prop where
  view : Relief L f g m
  input i : i≤n → ∀ x∈s,∀ y:V, mark T (Y x) (PowerSeries.coeff i (clouds R)) y= layers f i (x,m x+y)
  output i : i≤n → ∀ x∈s, aeval (Y x) (PowerSeries.coeff i (clouds (massaged (fun i j=> L.wick (T i) (T j)) R)))= layers g i x
section measure
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace V][BorelSpace V]
variable (μ:Measure V)[μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]
include μ
def measureT (L:Law V)(μ:Measure V): ℝ:= ∫ x,L.kern x ∂μ
lemma measure_pos (L:Law V) : 0< measureT L μ:= by unfold measureT; apply integral_exp_pos; exact (by simpa using! L.integrable_entry μ (A:=1) (Zone.Invoice.const (1:ℝ)) continuous_const)
variable {T Y} -- s not declared
variable {n :ℕ}{s:Set E}
lemma wing (h:Arc L Y T R f g m n s)(hp:Snug R)(i:ℕ)(hi:i≤n) (x:E)(hx:x∈s) : mural μ 1 f i x= (measureT L μ)*normTerm 1 g i x:= by
    let p:= PowerSeries.coeff i (breath (clouds R)); let v := kernel g x; have he(y):normTerm 1 f i (x,m x+y)=mark T (Y x) p y * (v*L.kern y):= by
      unfold normTerm
      rw [unclad]; rw [show kernel f (x,_)=v*L.kern y from ?_]; apply congr_arg₂ (·*·) ?_ rfl
      · unfold p mark; exact (expand_c (f:=layers f) (Y x + fun j=> T j y) i hi fun k hk => h.input _ hk _ hx y).symm
      unfold kernel v kernel Law.kern; rw [←Real.exp_add,h.view.shift]; congr 1; ring
    have hg := finish L T (Y x) μ hp i; rw [expand_c (f:=layers g) _ i hi (fun k hk=> h.output k hk x hx) ] at hg
    let A:= fun y:V=> mark T (Y x) p y*L.kern y; change ((∫ y, A y ∂μ)/measureT L μ)=_ at hg
    unfold mural; rw [← integral_add_right_eq_self _ (m x)]; simp_rw [add_comm _ (m x),he]; unfold normTerm; rw [unclad,←hg]; change _ =measureT L μ*((_/measureT L μ)*v)
    rw [show (∫ y, _ ∂μ)=v*(∫ y,A y ∂μ) from ?_]; · field_simp [ (measure_pos μ L).ne']
    · unfold A; rw [←integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun x=>?_); dsimp; ring
omit μ [μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ] in
lemma evolve {R:ℝ} (h:Radial.Stationary g) (n:ℕ): ∃ C,0≤C ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀ x∈closedBall (0:E) R, ‖projection 1 g t x-Zone.eval (normTerm 1 g) n t x‖ ≤ C*t^(n+1):= by
   obtain ⟨δ,D,k,hδ,hD,H⟩:= ((integrand (K:=1) contDiffAt_const h (c:=1) zero_lt_one).fits n).cost; let s := closedBall (0:E) R
   have hx : Continuous (fun x:E=> Radial.zone.w x^k*shade 1 x * kernel g x) := by unfold shade kernel; have hj: Continuous (Radial.zone (E:=E)).w:= continuous_const.add continuous_norm; have hg:= Smooth.continuousJet g 2; fun_prop
   obtain ⟨M,hM⟩:= (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hx.continuousOn
   refine ⟨D*|M|,mul_nonneg hD (abs_nonneg _),?_⟩; filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show 0<δ/(1+|R|) by positivity)), self_mem_nhdsWithin] with t ht (he:0<t) x hx
   have hu: t*Radial.zone.w x≤δ:= by apply le_trans _ ((lt_div_iff₀ (by positivity : 0<1+|R|)).1 ht).le; gcongr; change 1+_≤ _; linarith [mem_closedBall_zero_iff.mp hx,le_abs_self R]
   rw [show Zone.eval (normTerm 1 g) n t x = poly 1 g n t x from ?_]; swap; · unfold Zone.eval poly Zone.eval normTerm; simp only [smul_eq_mul,mul_assoc,Finset.sum_mul] -- order
   unfold projection poly; rw [← sub_mul,norm_mul,Real.norm_of_nonneg kernel_pos.le]; refine (mul_le_mul_of_nonneg_right (H x t he hu) kernel_pos.le).trans ?_; set T:= Radial.zone.w x; change D*T^_*_ * _ * kernel g x≤ _
   have hb:T^k*shade 1 x*kernel g x≤ |M|:= (le_abs_self _).trans ((hM x hx).trans (le_abs_self _)); nlinarith only [mul_le_mul_of_nonneg_left hb (by positivity : 0≤ D*t^(n+1))]
lemma relief (h:Arc L Y T R f g m n s)(hF:Radial.Stationary f)(hf:Measurable f)(hG: Radial.Stationary g)(hC:Snug R) (d:ℝ): ∃ δ>0, ∀ r>0,∃ D:ℝ,0≤ D ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀ (x:E), x∈s → x∈closedBall (0:E) d→ ∀ U:Set V, MeasurableSet U → disc t r⊆U → U⊆disc t δ → IntegrableOn (fun y:V=> projection 1 f t (x,y)) U μ ∧ ‖ash μ 1 f t U x-measureT L μ * Real.exp (-g (t•x)/t^2)‖≤D*t^(n+1) := by
    obtain ⟨c,hc,b,hb⟩:= hilly_ball h.view d
    obtain ⟨δ,hδ,H⟩:= perspective μ hF (K:=1) contDiffAt_const measurable_const hf hc hb n; refine ⟨δ,hδ,fun r hr=> ?_⟩; obtain ⟨D,hD,H⟩:= H r hr; obtain ⟨C,hX,hy⟩:= evolve (R:=d) hG n
    have hp := measure_pos μ L; refine ⟨D+measureT L μ*C,by positivity,?_⟩
    filter_upwards [H,hy] with t h₁ h₂ x hx hu U ha hf hw; obtain ⟨hv,hζ⟩:= h₁ U ha hf hw x hu; refine ⟨hv,?_⟩; let A:=measureT L μ; let q:= Zone.eval (normTerm 1 g) n t x
    rw [show Zone.eval (mural μ 1 f) n t x=A*q from ?_] at hζ; swap; · unfold q Zone.eval; rw [mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [wing μ h hC _ (by simp only [Finset.mem_range] at hi; omega) x hx]; unfold A; simp only [smul_eq_mul]; ring
    let P:=projection 1 g t x; rw [show Real.exp _=P from (by unfold P; rw [projection_eq]; simp)]
    calc
      _ ≤ ‖ash μ 1 f t U x-A*q‖+‖A*q-A*P‖:= by simpa only [dist_eq_norm] using dist_triangle (ash μ 1 f t U x) (A*q) (A*P)
      _ ≤ _:= by rw [← mul_sub,norm_mul, norm_sub_rev q,Real.norm_of_nonneg hp.le]; apply (add_le_add hζ (mul_le_mul_of_nonneg_left (h₂ _ hu) hp.le)).trans_eq; ring
end measure
end
end YM.Contacts.Milling
