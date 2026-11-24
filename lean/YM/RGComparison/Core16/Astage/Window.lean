import YM.RGComparison.Core16.Astage.Clocks
import YM.OPE.Log.Bottleneck
import YM.Extra.SOURCE_HISTORIES.Tide

/-!
# Upgrade cost for the two-window strategy

Use the weaker *physical* inverse throughout the shorter s-window, directly on coupling errors.
Can also be used to apply over long windows to errors that already earned a spatial gain. Compute
needed estimates on actual coupling and chart cross maps, **before extraction** so irrelevant
errors can still be projected. This estimates on the horizon-d *unit-root* system in the Formal
binding, `C.factory`! Not yet providing an all-address representative comparison. Not the sharp
Gram bound targeted by MatrixTicket. Don't use the latter to deduce the former.

Baseline rough prefix fares cannot be multiplied into the coupling accuracy *over the long return
to physical reference labels* -- obstruction shown below. Instead use only their relative
(in i,j) form on the log Λ_m soft subinterval. After earning **spatial** error, such as by
subtracting physical tested product and estimating source difference (open producer),
then full prefix costs fit. Alternatively use quotient-frame bootstrap on actual scalar/Gram
as in `Resolve`. Don't spend p-dependent powers per soft step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Window
open Filter Function Set Lattice RG Wilson Pert.Asymptotics Real Metric Witness OPE Columns
open Work.D01 Extra.Histories.Charts Next.UVStress
open Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (C:Family G)(H:C.Makes) (hG:G.Simple) {ι:Type*}{l:Filter ι}{j m N p:ι→ℕ}
local notation "q"=>C.path.levels
set_option quotPrecheck false
local notation "s"=>ruler C m
local notation "Λ"=>budgetLog C m
local notation "g"=>rho C m N p
local notation "y"=>frameTime C m

/- The official rough prefix pricing of the inverse quotient already > g^{-ANY} (in **coupling**
rate, not engineering). Sharp Gram could fix in higher goals; cannot be used in initial matching.
NB not claiming the inverse ITSELF is provably that large, only the fare. -/
include hG H in
lemma prefix_not_affordable (d e k:ℕ) (ht:Tendsto m l atTop)(hk:∀ᶠ i in l,m i ≤ N i):
    Tendsto (fun i=> (C.S.a (m i) ^ (d-(e+1)) * fare C (m i) d e) * g i^k) l atTop := by
    let Q := q; let A i := ruler C m i; let a := C.S.a; let n:=d-(e+1); let z (m:ℕ):= gel Q m
    have HA:= large_s C ht
    -- combine with g^2 * scale tends positive
    let t:(ι→ℝ):= g
    have hk' :∀ᶠ i in l,0 < g i:= (pace (p:=p) H hG ht hk).pos
    have hp:= beta_relation (p:=p) H hG ht hk
    have he':Tendsto (fun i=> t i^2 * A i) l (𝓝 (G.slopeConstant)⁻¹):=by
       have hx := (hp.mul (linear_s C ht)).inv₀ (mul_ne_zero one_ne_zero (Gauge.slopeConstant_pos hG).ne')
       rw [one_mul] at hx
       apply hx.congr'; filter_upwards [hk] with i hi; let a' := C.path.β (N i) (p i) (m i); have hb:0<a':= Overlay.beta_positive H.wilson hi; let Y:=(q).clock.hatBeta (m i); have hQ:0<Y:=zero_lt_one.trans ((q).fits.delayed _); change (a' / Y * (Y/A i))⁻¹=(sqrt a')⁻¹^2 * A i; rw [div_mul_div_cancel₀ hQ.ne', inv_pow,sq_sqrt hb.le,inv_div,div_eq_mul_inv,mul_comm]
    have hu:= ((Log.gel_too_big C k).comp ht).atTop_mul_const (pow_pos (C.S.a_pos (C.ref d)) n)
    have hh:= hu.atTop_mul_pos (pow_pos (inv_pos.mpr (Gauge.slopeConstant_pos hG)) k) (he'.pow k)
    apply tendsto_atTop_mono' (l:=l) _ hh; filter_upwards [hk',HA.eventually_gt_atTop 0, ((pace (p:=p) H hG ht hk).pays (large_Λ C hG ht)|>.tends (by norm_num) (large_Λ C hG ht)).eventually (ge_mem_nhds zero_lt_one)] with i hi hA h
    let v:=(q).params (m i); have hf:0 ≤ z (m i):= zero_le_one.trans (gel_pos ..); have hv:0<v.columns:=zero_lt_one.trans_le v.columns_ge
    let a' := a (C.ref d); let b':= a (m i); have hx:0<b':=C.S.a_pos _; have hb:0<a':=C.S.a_pos _
    change z (m i) / A i^k * (a'^n)* (g i ^2 * A i)^k ≤ b'^n*(z (m i) * (1+v.columns)* (a'/b')^n)*g i^k
    calc _ = z (m i)*a'^n*(g i^2)^k:=by rw [mul_pow]; have hp: A i≠0:=hA.ne'; field_simp 
         _ ≤ z (m i)*(1+v.columns)* a'^n* (g i)^k:=by
             have ht: g i^2 ≤ g i:= by rw [pow_two]; exact mul_le_of_le_one_left hi.le h
             have he' : z (m i) ≤ z (m i)*(1+v.columns):= le_mul_of_one_le_right hf (le_add_of_nonneg_right hv.le); gcongr ?_*a'^n* ?_^k
         _ = _:=by rw [div_pow]; field_simp 
-- relative price
lemma short_price (T:Levels G)(ε:ℝ)(he:0<ε) : ∀ᶠ i in atTop, ∀ k≥i,
    columnLogs T k-columnLogs T i ≤ ε*(T.S.scale k-T.S.scale i):=by
    have hd : Tendsto (fun i : ℕ => ((T.clock.J (i+1):ℝ)^2)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp (T.fits.deep.comp (tendsto_add_atTop_nat 1))))
    apply (eventually_forall_ge_atTop.mpr (hd.eventually (ge_mem_nhds he))).mono
    intro i hi k hk; induction hk with
    | refl=> simp
    | step hk IH=> rename_i k; rw [columnLogs_succ,Schedule.scale_succ]; let p':= T.params (k+1); have hQ : Real.log p'.columns ≤ ε* Real.log (T.S.block k).val:= by
                     apply le_trans _ ((div_le_iff₀ (show 0 < Real.log (T.S.block k).val from Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1<3) (T.S.block_large k))))).mp ((T.fits.logCost k).trans (hi k hk)))
                     apply Real.log_le_log (zero_lt_one.trans_le p'.columns_ge)
                     unfold p'; linarith only [p'.paths_pos, inv_pos.mpr p'.width_pos, p'.clip.radius_pos,p'.price_pos]
                   linarith only [hQ, IH]

lemma soft(hv:Tendsto j l atTop) {b:ℝ}(hb:0<b)
    (hp:∀ᶠ i in l, j i ≤ m i) (hz:∀ᶠ i in l,(s) i - C.S.scale (j i) ≤ b*Λ i) :
    RateLE l Λ (fun i=> exp (columnLogs q (m i) - columnLogs q (j i))) 0:=by
    intro w hw; filter_upwards [hv.eventually (short_price q _ (div_pos hw hb)),hp,hz] with i hi hg he
    rw [Real.norm_of_nonneg (exp_pos _|>.le)]; apply exp_monotone
    exact (hi (m i) hg).trans ((mul_le_mul_of_nonneg_left he (div_pos hw hb|>.le)).trans_eq (by rw [← mul_assoc,div_mul_cancel₀ _ hb.ne']))

variable (d N' p':ℕ) {i k:ℕ}
local notation "W"=> (fun i=>Extra.Histories.Charts.window C H d i N' p')
local notation "S"=>C.labels.level d
local notation "μ"=>(C.labels.level d).coeffSize
lemma relative_inner (u:C.label d)(hi:C.ref d ≤ i) (hk:i≤k) (hz:k≤N'):
    μ (W k u) ≤ exp (columnLogs q k - columnLogs q i) * μ (W i u):=by
    induction hk with
    | refl=> simp
    | step hk IH=> rename_i k; let M:=((q).params (k+1)).columns; let t j:= W j u; have hx:0 < M:= zero_lt_one.trans_le ((q).params (k+1)).columns_ge; dsimp only
                   have hc:= (C.factory d N' p'); have hf:= H.calibrated d N' p' (hi.trans (Nat.le_trans hk ((Nat.le_succ _).trans hz))); have h : μ (t (k+1)) ≤ M * μ (t k):= by
                      rw [show t k=_ from peek C H _ _ _ _ (hi.trans hk) (k.le_succ.trans hz) _,show t (k+1)=_ from peek C H _ _ _ _ (hi.trans (Nat.le_trans hk k.le_succ)) hz _]; exact hf.back _ (hi.trans hk) hz _
                   refine h.trans ((mul_le_mul_of_nonneg_left (IH (k.le_succ.trans hz)) hx.le).trans_eq ?_); rw [columnLogs_succ, show _+log ((q).params (k+1)).columns- _= log M+(columnLogs q k-columnLogs q i) by dsimp [M]; ring,exp_add,exp_log hx,mul_assoc]
lemma relative_outer (u:C.label d)(hi:C.ref d ≤ i) (hk:i≤k) (hz:k≤ N'):
    μ (W i u) ≤ exp (columnLogs q k - columnLogs q i) * (C.S.a i / C.S.a k)^d * μ (W k u):=by
    induction hk with
    | refl=> simp [(C.S.a_pos i).ne']
    | step hk IH=>
       rename_i k
       apply (IH (k.le_succ.trans hz)).trans
       let x j:= μ (W j u); let z:= exp (columnLogs q k-columnLogs q i); let Y:=((q).params (k+1)).columns; let R:ℝ:=(C.S.block k).val; let a:= C.S.a i; let b:=C.S.a k
       have he :0 < a:=C.S.a_pos _; have hx:0<b:=C.S.a_pos _; have hZ:0<z:= exp_pos _; have hr:0<R:= Nat.cast_pos.mpr (C.S.block k).property; have hy:0 < Y:= zero_lt_one.trans_le ((q).params (k+1)).columns_ge
       have h:x k≤ Y*R^d*x (k+1):=by
           unfold x; rw [show W k u = _ from peek C H _ _ _ _ (hi.trans hk) (k.le_succ.trans hz) _,show W (k+1) u=_ from peek C H _ _ _ _ (hi.trans (Nat.le_trans hk k.le_succ)) hz _]; exact ((H.calibrated _ _ _ ((hi.trans (Nat.le_trans hk k.le_succ)).trans hz)).front k (hi.trans hk) hz _)
       rw [columnLogs_succ, add_sub_right_comm, Real.exp_add, Real.exp_log hy]; change z*(a/b)^d*x k ≤ z*Y* (a/_ )^d * x (k+1); rw [Schedule.a_step]; change _ ≤ z*Y*(a/(b/R))^d*x (k+1); refine (mul_le_mul_of_nonneg_left h (show 0≤ z*(a/b)^d by positivity)).trans_eq ?_; field_simp; rw [← mul_pow]; ring_nf

-- purchase the commonly needed composition over soft windows, *one uniform bound* on both
-- directions (engineering factor separately tracked). use oriented or threshold later if budget.
include hG
lemma pays_soft {b ζ:ℝ} (hb:0<b)(hζ:0<ζ)(hi:Tendsto m l atTop)(hk:Tendsto j l atTop)
   (hK:∀ᶠ i in l, j i ≤ m i)(hf:∀ᶠ i in l, m i ≤ N i)(hs:∀ᶠ i in l,s i-C.S.scale (j i) ≤ b*Λ i):
   ∀ᶠ i in l, let u:= cross C H d (N i) (p i) (j i) (m i); ∀ z:C.label d, μ (u z) ≤ (g i)^(-ζ) * μ z ∧
      μ (u.symm z) ≤ (g i)^(-ζ) *(C.S.a (j i)/C.S.a (m i))^d * μ z:= by
    have hx:= ((pace (p:=p) H hG hi hf).rpow (-ζ)).outweigh (soft C hk hb hK hs) (by linarith only [hζ]) (large_Λ C hG hi)
    filter_upwards [hx,hK,hf,hk.eventually_ge_atTop (C.ref d)] with i hi hK hn hm
    intro u z
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hi
    constructor
    · let v:= (Extra.Histories.Charts.window C H d (j i) (N i) (p i)).symm z
      calc _ ≤ exp (columnLogs q (m i)-columnLogs q (j i))*μ z:=by simpa only [v,ContinuousLinearEquiv.apply_symm_apply] using! relative_inner C H d (N i) (p i) v hm hK hn
           _ ≤ _:= mul_le_mul_of_nonneg_right hi (Work.G08.size_nonneg ..)
    let a:= (Extra.Histories.Charts.window C H d (m i) (N i) (p i)).symm z
    calc _ ≤ exp (columnLogs q (m i)-columnLogs q (j i)) * (C.S.a (j i)/C.S.a (m i))^d * μ z:=by simpa only [a,ContinuousLinearEquiv.apply_symm_apply] using! relative_outer C H d (N i) (p i) a hm hK hn
         _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)) (Work.G08.size_nonneg ..)
end YM.RGComparison.Core16.Astage.Window
