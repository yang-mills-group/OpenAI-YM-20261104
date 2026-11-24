import YM.MS.Drops.Month
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
open Asymptotics
abbrev pale (u:ℤ)(s:ℝ):= exp s ^ u
abbrev Outlay (l:Filter ℝ)(X:ℝ→ℂ)(u:ℤ) : Prop:= X =O[l] (pale u)
variable (L K:Degree G) {u:ℤ} {l:Filter ℝ}
lemma width (x:E4) : Outlay l (γX L K x) (-(hgt L K:ℤ)):= by
    obtain ⟨C,hC,hA⟩:= global L K; apply Asymptotics.IsBigO.of_bound C; filter_upwards with i; rw [Year,norm_smul, mul_comm C ]; unfold pale; rw [ zpow_neg,zpow_natCast ]; exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
lemma whisper_s (x:E4)(hx:x≠0) (n:ℕ): Outlay atBot (fun s=>γX L K x s - ( Prayer.gleam L K x :ℂ)) (n:ℤ) := by
   let k:= hgt L K; let p:= n+k; obtain ⟨C,hC,hv⟩ := born0 L K p;
   have h':0<‖x‖:= norm_pos_iff.mpr hx
   apply Asymptotics.IsBigO.of_bound ( C/ ‖x‖^p ); filter_upwards [ tendsto_exp_atBot.eventually ( Iio_mem_nhds h' ) ] with s hs; replace hs:exp s <‖x‖:=hs; let r:= exp s; have ht:0<r:= exp_pos s; let y:=r⁻¹ • x; have hu:‖y‖=r⁻¹*‖x‖:= by rw [norm_smul_of_nonneg ( inv_nonneg.mpr ht.le )];
   have hm := hv y ( by rw [hu]; field_simp; exact hs.le ); rw [Year, Right L K x hx s, exp_neg ]; change ‖(r^k)⁻¹ • γX L K y 0 - ↑((r^k)⁻¹ * Prayer.gleam L K y)‖ ≤ _
   rw [ Complex.ofReal_mul, ← Complex.real_smul, ← smul_sub,norm_smul_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)) ]; apply (mul_le_mul_of_nonneg_left hm ( by positivity )).trans_eq; unfold pale; rw [zpow_natCast,norm_of_nonneg (pow_nonneg ( exp_pos _|>.le ) _),hu]; change _= _* r^n; unfold p; rw [mul_pow, inv_pow ]; simp_rw [ pow_add ]; field_simp
abbrev Sharp0 (f:ℝ→ℂ): Prop:= ∀ j:ℕ,Outlay atBot f j
abbrev Tall0 (f:ℝ→ℂ): Prop:= ∃ j:ℤ, Outlay atBot f j
lemma shorn0 (k:ℤ): Outlay l (0:ℝ→ℂ) k:= isBigO_zero ..
lemma quieter (x:ℂ): Outlay l (fun _=>x) 0:= by rw [Outlay, show pale 0= fun _=> (1:ℝ) from funext fun t=>by simp [pale] ]; exact isBigO_const_const _ one_ne_zero _ -- check syntax
lemma softU (l:Filter ℝ) (x y:ℝ→ℂ)(i j:ℤ)(hx: Outlay l x i)(hy: Outlay l y j): Outlay l ( x*y ) (i+j):= by simp only [Outlay,show pale (i+j)= pale i*pale j from funext fun s=> zpow_add₀ ( exp_pos s|>.ne' ) i j ]; exact hx.mul hy
variable {f g:ℝ→ℂ}{i j:ℤ}
lemma north (h: Outlay atBot f j)(hp:i≤j): Outlay atBot f i:= by refine h.trans ( IsBigO.of_bound 1 ?_ ); filter_upwards [ eventually_le_atBot (0:ℝ) ] with x hx; simp only [one_mul,pale,Real.norm_of_nonneg ( zpow_nonneg ( exp_pos _|>.le ) _ ) ]; exact zpow_le_zpow_right_of_le_one₀ ( exp_pos x ) ( Real.exp_le_one_iff.mpr hx ) hp
lemma tall0 (h:Sharp0 f): Tall0 f:= ⟨_, h 0⟩
lemma sunny0 (h:Tall0 f)(he:Tall0 g): Tall0 (f+g):= by obtain ⟨u,hu⟩:=h; obtain ⟨v,hv⟩:=he; exact ⟨min u v,( north hu ( min_le_left .. ) ).add ( north hv ( min_le_right .. ) )⟩
lemma shiver (h:Tall0 f)(hv:Tall0 g): Tall0 (f*g):= by obtain ⟨u,hu⟩:=h; obtain ⟨v,hv⟩:=hv; exact ⟨ u+v, softU _ _ _ _ _ hu hv⟩ -- unusual ..
lemma tallC (p:ℂ): Tall0 (fun _=>p):= ⟨0,quieter p⟩
lemma solar0 (h:Tall0 f)(he:Sharp0 g): Sharp0 (f*g):= by obtain ⟨i,hi⟩:= h; exact fun j=> north ( softU _ _ _ _ _ hi (he ( ( ( j:ℤ )- i ).toNat )) ) (by omega)
lemma solar1 (h:Tall0 f)(he:Sharp0 g): Sharp0 (g*f):= mul_comm f g ▸ solar0 h he
lemma dusk (h:Sharp0 f): Tendsto f atBot (𝓝 0):= by refine (h 1).trans_tendsto ?_; unfold pale; simpa using tendsto_exp_atBot
lemma eitherI (hp:Outlay atTop f i)(he:i<0): Tendsto f atTop (𝓝 0) := hp.trans_tendsto ((tendsto_zpow_atTop_zero he).comp tendsto_exp_atTop) -- names
end YM.MS.Drops
