import YM.LocalLTE.Concert.Kits
/-!
# Physical offer through budget. step.J uniform all backgrounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{n:Side} (P:Rep G n) (B:BudgetPoint)
variable {V α :Type}[DecidableEq V] (R:Census V)
open FrameBox Grove Cabana
open AnalyticBridge VerifiedReset Collection
open Animals ConnectedActivityE6 Blaze Brush
variable [Fintype α]
variable (K:LoopBank G n R α)(b d:ℕ)(μ:ℝ)
namespace LoopBank
local notation "A₁"=> wall R K b
local notation "V₁"=> wires R K b
local notation "f₀"=>realSignal R K
local notation "f₁"=>signal R K
variable (A:(i:α)→Grove (K.scene i))
local notation "H₀"=> baked P R K b
local notation "g₀"=> modelRain R K b d μ A
local notation "g₁"=> model R K b d μ A
local notation "fB"=> (fun i=>K.wires R b i)
variable {x a T J c d' z φ η σ:ℝ} (hk:Reliable G μ a)
variable (hX:Legit R K b J T) (hq:∀ i,P.p.supBounds (K.scene i) (wires R K b i) (realSignal R K i-modelRain R K b d μ A i) z)
local notation "C'"=> slotPay G J b P.p.order P.p.power
local notation "P'"=> P.p
-- b footprint and U markers. scale weight cap r. price favors stricter costs; YES Y booked afterL high.
local notation "u₀"=> payment P.p T C' b
local notation "q₀"=> payment P.p T z b
local notation "k₀"=> payment P.p T (C'+z) b
local notation "L'"=> ((Fintype.card α:ℕ):ℝ)
def footprintCost (b:ℕ)(A:ℝ) := Real.exp (A*ballCost (b+1))
variable (w:V→ℝ) (hs:∀ i,0<w i)(hr:∀ i,w i ≤ η)(hz:η ≤ 1)
local notation "S₀"=> footprintCost b P.p.supportExponent
-- cap amounts. Epre logs.A.
include hX hs hr hz
variable (hΦ:0≤η)
omit [Fintype α] in
lemma headT (i:α): Poly.toll w (K.select i)≤η:=by
    obtain ⟨p,hp⟩:= hX.honest i; unfold Poly.toll; rw [← mul_prod_erase _ _ hp]; refine mul_le_of_le_one_right (hs p|>.le) ?_|>.trans (hr p)
    exact prod_le_one (fun i _=> hs i|>.le) (fun i _=> (hr i).trans hz)
omit [Fintype α] in
lemma spaceZ (x:ℝ)(hx:0≤x)(i:α): Poly.toll w (K.select i)*P.p.mass (K.wires R b i) x ≤ η*(S₀*x):=by
   apply mul_le_mul (headT R K b hX w hs hr hz i) _ (mul_nonneg (Real.exp_pos _).le hx) ((Poly.worth hs _).le.trans (headT R K b hX w hs hr hz i))
   apply mul_le_mul_of_nonneg_right _ hx; apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_left _ (P.p.exponent_pos.le)
   apply Nat.cast_le.mpr; apply YM.PhysicalNext.Repeat.Scarf.standing (b+1) P.p -- edit
   exact Nat.le_mul_of_pos_right _ P.p.B_pos
include hΦ
lemma priceFire (k:ℝ)(hk:0≤k)(m:ℕ)(hα:Fintype.card α ≤ m): ∀ v:V,SumBudget (fun i=> if v∈(K.select i).val then Poly.toll w (K.select i)*P.p.mass (V₁ i) k else 0) ((m:ℝ)*(η*(S₀*k))):=by
   intro v; let g (i):= η*(S₀*i); have he:0 ≤ g k:=mul_nonneg hΦ (mul_nonneg (Real.exp_nonneg _) hk); refine ⟨fun i=> ?_,Summable.of_finite,?_⟩
   · dsimp only; split; exact mul_nonneg (Poly.worth hs _).le (mul_nonneg (Real.exp_nonneg _) hk); exact le_rfl
   rw [tsum_fintype]; refine ((sum_le_sum (g:=fun _:α=> g k) fun i _=> ?_).trans_eq (show ∑ _:α, g k= L'*g k from by simp)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hα) he)
   split; exact spaceZ P R K b hX w hs hr hz k hk i; exact he
local notation "Y'"=> T*(C')
variable (m:ℕ)(hrm:Fintype.card α ≤ m) (hp:0≤σ) (hC:0≤ slotPay G J b P.p.order P.p.power)
-- K budget using T ONLY not at η scale.
abbrev fog (m b:ℕ)(κ:ℝ):= Real.exp (m*(ballCost (b+1):ℝ)*κ)-1
-- K finite exponent buys even on unscaled. 
def gross (m b:ℕ)(p:BudgetPoint)(κ T:ℝ):= fog m b κ*(1+footprintCost b p.supportExponent*T)^m
include hp hrm hC
omit hΦ
lemma tender : chargeFog P (H₀) σ * chargeMark P H₀ (fun _=> T*C') w ≤ gross m b P.p σ (T*(C')):=by
    let Z:= V₁
    have hb : (coastK P (H₀)).card ≤ m*ballCost (b+1):=by
       apply (card_biUnion_le ..).trans; refine (sum_le_sum (g:=fun _=> ballCost (b+1)) (fun i _=> neighbors_card _ (K.scene i))).trans ?_; simp only [sum_const,nsmul_eq_mul,card_univ]; exact Nat.mul_le_mul_right _ hrm
    have ht:0≤T:= hX.possible.2; let k:= T*C'; have hk:0≤ k:=mul_nonneg ht hC; let M (i:α):= 1+Poly.toll w (K.select i)*P.p.mass (V₁ i) (T*C'); have h(i):1≤ M i:=le_add_of_nonneg_right (mul_nonneg (Poly.worth hs _).le (mul_nonneg (Real.exp_nonneg _) hk)); have hg:0 ≤ S₀*k:=mul_nonneg (Real.exp_nonneg _) hk
    have hc:chargeFog P (H₀) σ ≤ fog m b σ:=sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hp)) _
    refine mul_le_mul hc ?_ (show 0≤∏ i:α,M i from Finset.prod_nonneg (fun i _=> zero_le_one.trans (h i))) (show 0 ≤ fog m b σ from sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    refine le_trans (le_trans (b:= ∏ _:α,(1+S₀*k)) ?_ (le_of_eq (show ∏ i:α,(1+S₀*k)=(1+S₀*k)^Fintype.card α from by simp))) (pow_le_pow_right₀ (le_add_of_nonneg_right hg) hrm)
    exact Finset.prod_le_prod (s:=Finset.univ) (fun i _=> zero_le_one.trans (h i)) (fun i _=> show M i≤ _ from add_le_add le_rfl ((spaceZ P R K b hX w hs hr hz _ hk i).trans (mul_le_of_le_one_left hg hz)))
section enroll
-- leg output input Radial/slip earnings
variable [Nonempty V]
include hp hq hk hX hC hrm hΦ
variable (he:HasSlots P.p P.activities)(hy0:P.activities.Valid P.p d' σ)
variable (h':0≤z)
local notation "m₁"=> P.p
local notation "Z'"=> (Port.posta P R (H₀))
local notation "F'"=> Port.crystal P (H₀) (g₁)
local notation "T'"=> Port.thaw P (H₀) (g₁)
include he hy0 h'
abbrev costAP(m:ℕ)(w:ℝ)(p:BudgetPoint)(b:ℕ)(u T:ℝ):= (m:ℝ)*(w*(footprintCost b p.supportExponent*(payment p T u b)))
local notation "V0"=> costAP m η P.p b
local notation "K'"=> gross m b P.p σ (T*C')
lemma crystals (ν κ y :ℝ)(hν:0<ν)(hκ: 0≤κ) (hy:∀ i,w i*‖K.units i‖ ≤ y) (hx:gross m b P.p σ (T*C') ≤ κ*ν): (Z').Active∧(F').Active∧(T').Active∧ (Z').Radial w y (V0 C' T) κ ν ∧ (F').Radial w y (V0 (C'+z) T) κ ν ∧ (T').Radial w 0 (V0 z T) κ ν :=by
    let X':=H₀; let p':= P.p; let f:=g₁; let x:=C'; let U (i:α):=Y'; let a:=u₀; let k:=k₀; let q:=q₀; let t':=T
    have ha(y:ℝ)(hh:0≤y):0 ≤ payment p' T y b:= mul_nonneg (mul_nonneg hX.possible.2 (sunny ..)) hh
    have hv:= frostD P R X' he (raysP P R K b hX) hy0
    have hu:= LoopBank.priceFire P R K b hX w hs hr hz hΦ
    have hj i v (hv:v∈ (K.select i).val): P.p.supBounds (K.origin v) (V₁ i) (X'.H i) a:= LoopBank.wind P R K b hX i _ _ (wins P R K b hX i) (glow P R K b hX i) v hv
    have hG:= tender P R K b hX w hs hr hz m hrm hp hC; have hH:= frosty P X' he hy0 U (fun _=> a) (fun i V=>legalK P R K b hX i V) (fun _=>ha _ hC) hj w hs κ y (V0 x T) ν hy hν (hG.trans hx) (hu _ (ha _ hC) m hrm)
    have he' i:= LoopBank.aroma P R K b d μ A hk hX i; have hz := starsV P X' f (fun i=> (he' i).1) (fun i=>(he' i).2) hv
    have hg (j:α)(v)(hv:v∈ (K.select j).val):= aromaPay P R K b d μ A hk hX hq j v hv
    exact ⟨hv,hz.1,hz.2,hH,pollen P X' f hH hκ (fun _=>k) (fun _=>q) (fun _=>ha _ (add_nonneg hC h')) (fun _=> ha _ h') (fun i s h=>(hg i s h).2) (fun i s h=>(hg i s h).1) (hu _ (ha _ (add_nonneg hC h')) m hrm) (hu _ (ha _ h') m hrm) ⟩
omit hp hq hk hX hrm hΦ he hy0 h' hC hs hr hz
lemma illuminant (u v:ℕ)(hp:d≤u+1)(hv:b+1 ≤ v) : Port.Shine R F' u v μ:=by
   refine Port.appeal P H₀ g₁ (fun i=> ?_); let y:= V₁ i; let x':= K.scene i; have hh:x'∈ y:=(neighbors_mem ..).2 (by simp [x'])
   refine ⟨K.scene i,hh,(fun j hj=> ((neighbors_mem ..).2 (((neighbors_mem ..).1 (show j∈ y from hj)).trans hv))), b, by omega, A i,fun k=> ?_⟩
   exact Price.rp_raise (A i) (Port.huesPam (A i) (g₀ i) d ⟨_,rfl⟩ _ _ k) hp -- notation.i
end enroll
end LoopBank
end YM.LocalLTE.Port
