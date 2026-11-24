import YM.MSbar.Cottage.Posture
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U: Config G f}{R: Rep G f}{σ C T H K A B a b v r δ w β:ℝ}{M k m:ℕ}
open Finset RG.PathData Tree Push.Uniform Pressure
variable (F:Forest S.ratio) (X :Support f)
open SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric
variable (J:Voice G) (Q: Config G c) (μ: Positions (Key F G))(Y:Support f)
set_option quotPrecheck false
local notation "I!"=> IV F (board F X) G
local notation "U!"=> Config G f
local notation "q!"=> twirl (G:=G) (S:=S) F (board F X)
local notation "o!"=> fence F (board F X) G
-- exponent log model BEFORE HAAR (use project Jacobian later)
variable (i:S.Choices)(p:Palisade)(x: Positions (Primary c G)) (h:Grants i R F p m)
local notation "W"=> (represent (tint G (Exterior.Body 1 c) x))
local notation "Y!"=> hotel F X Y J W μ A B
local notation "z!"=> chambers F Y J W μ
local notation "f!"=> rental F J R Y i W μ
local notation "L"=> (R.exponent ∘ z!)
local notation "Ω!"=> priced F i R.clip R.path
local notation "R!"=> R.p.threshold
-- Choice.Posture quantity ∆. `B` bandwidth and K full bounds
local notation "h!"=>Posture p J F A B v K M k X Y x μ R.p
variable (g:Clear G J) (q:Posture p J F A B v K M k X Y x μ R.p)
namespace Posture
variable {p J F X Y x μ}
include q
-- numeric frame.K. Y copy. Healthy flags.Read extra halo
local notation "Ik"=> youth F Y
local notation "Uθ"=> "+unused"
local notation "E'"=> (silkRoad C σ δ T R.beta X.card M R.p k)
variable (t:I!) (sold:R.Lawful σ C T δ w)(hD:S.patch.Branches S.kernel G)(hB: Decent R.clip R.p)(hz:0≤ R.beta)
include g
include sold hB hz h
lemma washout {k':IV F (board F X) G} (hU:U∈Y!)(hx:q! k' U∈hotel F X Y J W μ A B) : 
      let e:=2*B; let d:= rented F Y J W μ (q! k' U)-rented F Y J W μ U; ‖d‖≤ e ∧ wash d ≤ (Y.card*(4:ℝ))*Fintype.card G.ColorIndex*e:=by
    intro e d
    have hl (U)(h:U∈ hotel F X Y J W μ A B): ‖rented F Y J W μ U-μ‖ ≤ B:= leanOn F X Y J W μ g q.extendsX h q.goes q.height
    have he : ‖d‖ ≤ e:= by
         unfold d; rw [← sub_sub_sub_cancel_right _ _ μ]; exact ((norm_sub_le ..).trans (add_le_add (hl _ hx) (hl _ hU))).trans_eq (by unfold e; ring)
    let M:=(board F Y ×ˢ (univ:Finset G.ColorIndex)); let f i:= |d i|
    have hb i: f i ≤ e:= le_trans (norm_le_pi_norm d i) he
    have hg(i:Key F G) (ht:i∉M): d i=0:=by
        let j:= i.1; have ht:j∉board F Y:=fun hb=>ht (mem_product.mpr ⟨hb,mem_univ _⟩)
        unfold d; rw [Pi.sub_apply]; change tint G _ (rented F Y J W μ (q! k' U)) j i.2-tint G _ (rented F Y J W μ U) j i.2=0; simp_rw [rented, ContinuousLinearEquiv.apply_symm_apply]; simp only [if_neg ht, sub_self]
    have hr : (board F Y|>.card :ℝ)≤ Y.card*(4:ℝ):= by exact_mod_cast boardC F Y
    refine ⟨he,?_⟩; change ∑ i,f i≤ _; rw [← sum_subset (subset_univ M) (fun i _ hx=>by unfold f; rw [hg i hx,abs_zero])]; apply (sum_le_sum (fun i _=> hb i)).trans; rw [sum_const,nsmul_eq_mul,card_product, card_univ, Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) ((norm_nonneg _).trans he)
-- Hessian estimate.C.L Σ.B
omit q g sold hB hz h in
def vapor (p:Palisade)(K B w:ℝ) :=
   let j:= p.coords*countCost p.a; let C:= p.density*j; let I:=K*C*j*K; w*((2*B*C+ I)+(K*C+I))
omit q g sold hB hz h in
def wLevel (G:Gauge)(y:ℕ)(w:ℝ) := (y*(4:ℝ))*Fintype.card G.ColorIndex*(2*w)
omit q g sold hB hz h in
def wSize (G:Gauge)(P:BudgetPoint)(σ C δ T β:ℝ)(M y x:ℕ)(p:Palisade)(K B:ℝ) := outset P σ C δ T β M x + β* vapor p K B (wLevel G y B)
lemma clover (t:IV F (board F X) G)(hU:U∈Y!)(hx:q! t U∈hotel F X Y J W μ A B) : 
    |f! (q! t U)-f! U| ≤ wSize G R.p σ C δ T R.beta M Y.card X.card p K B:= by
    let H:= z! U; let V:= q! t U; let A':=z! V; have H₀:= (planT g q t hU hx); have hF:= formal_edge H₀.2 sold q.stone hB hz
    let d:= rented F Y J W μ U; let c:= rented F Y J W μ V
    have hxW : ‖meetVar x d‖≤ K:= (pose g q hU).2.1; obtain ⟨ht,hT⟩:=washout i h g q sold hB hz hU hx; let Jx:=wLevel G Y.card B; have hp : K+2*B<p.delta:=q.room.trans_le p.enroll
    let v:=vapor p K B Jx; let w₁:= p.coords* countCost p.a; let k:= p.density*w₁
    let w₀:= c-d; have ht':‖w₀‖ ≤ 2*B:= ht; have hL: wash w₀≤ Jx:=hT
    let I':= (K*k*w₁*K); have he:w₀+c=c+w₀:=add_comm ..; let z:=fderiv ℝ (Slope (priced F i R.clip R.path)) 0 (meetVar x d); let b:=blush w₀ z
    have hP: |(priced F i R.clip R.path) (meetVar x c) - (Ω!) (meetVar x d)|≤ v := by
       have hh:= slip h.buys hxW ht' hp; rw [show d+w₀=c by unfold w₀; abel] at hh
       have hb:0≤ B:= q.height; have hk:0≤ K:=(norm_nonneg _).trans hxW
       have hm :0 ≤ w₁:= mul_nonneg (Nat.cast_nonneg _) (count_pos h.buys.pos_a|>.le); have hC':= h.buys.pos_C; have hK:0≤ k:=mul_nonneg hC'.le hm; have hI:0≤ I':=by unfold I'; positivity
       have hζ : |b| ≤ Jx * (K*k+I'):= (washes ..).trans (mul_le_mul hL (sight_range h.buys _ hxW (by linarith)) (norm_nonneg _) ((wash_nonneg _).trans hL))
       let s' := priced F i R.clip R.path (meetVar x c)-priced F i R.clip R.path (meetVar x d)
       have hg:|s'-b| ≤ Jx*(2*B*k+I'):= hh.trans (mul_le_mul_of_nonneg_right hL (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hb) hK) hI))
       change |s'| ≤ _; rw [show s'=s'-b+b by abel]; exact ((abs_add_le ..).trans (add_le_add hg hζ)).trans_eq (by unfold v vapor I' k w₁; ring)
    let q₀:= f! V - f! U; let J':= outset R.p σ C δ T R.beta M X.card; rw [written,written] at hP; let a:= noiseTaylor S W (z! V) i-noiseTaylor S W (z! U) i; let u:=mainTerm R.clip R.path (z! V)-mainTerm R.clip R.path (z! U)
    have ht : q₀+ R.beta*(a+u) = - ((R.exponent (z! U)- R.exponent (z! V))+ R.beta*(mainTerm R.clip R.path (z! U)-mainTerm R.clip R.path (z! V))):= by unfold q₀ rental a u; ring
    have hf₀:|a+u| ≤ v:=by
        rw [show a+u=tested F i R.clip R.path (tint G _ x) (tint G _ c)-tested F i R.clip R.path (tint G _ x) (tint G _ d) from ?_]; · exact hP
        change noiseTaylor S W (z! V) i-noiseTaylor S W (z! U) i+(mainTerm _ _ (z! V)-mainTerm _ _ (z! U))=(mainTerm _ _ (z! V)+noiseTaylor S W (z! V) i)-(mainTerm _ _ (z! U)+noiseTaylor S W (z! U) i); abel
    change |q₀| ≤ _; rw [show q₀=q₀+R.beta*(a+u)-R.beta*(a+u) by abel]; refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [ht,abs_neg]; exact hF
    rw [abs_mul,abs_of_nonneg hz]; exact mul_le_mul_of_nonneg_left hf₀ hz
-- cost under transport twisting: normalized off other groups.
include hD
lemma charge (t:IV F (board F X) G)(hU:U∈Y!)(hx:q! t U∈hotel F X Y J W μ A B) :
    S.density R.beta U W * Real.exp (f! (q! t U)) *Real.exp (R.exponent U- R.exponent (q! t U)) ≤ Real.exp (silkRoad C σ δ T R.beta X.card M R.p k) * (S.density R.beta (q! t U) W* Real.exp (f! U)):=by
    let V:= q! t U; have H':= (planT g q t hU hx); let ε:= silkRoad C σ δ T R.beta X.card M R.p k
    have hp:=copied sold H'.1 q.bank H'.2 q.stone hB hz; let d:=S.density R.beta V W; have hd:0 ≤ d:= (S.isKernel hD R.beta).positive ..
    have ht:= bursts i h g q hD t hU hx
    have hy(Z':Config G f): R.exponent (canoe (S:=S) F Z')=R.exponent Z':=Further.DenseMixedKernels.Throng.phase sold _ _
    rw [hy,hy] at hp; have he : -R.beta*sigh S i W (z! U) (z! V) + (f! V + (R.exponent U-R.exponent V)) ≤ ε+f! U := by
       unfold rental sigh; unfold V ε; linarith only [(abs_le.mp hp).2]
    rw [ht]; change d*_ * _ * _ ≤ Real.exp ε*(d*_); rw [mul_assoc (d*_ ),mul_assoc d, mul_left_comm (Real.exp ε) d,←Real.exp_add,←Real.exp_add,←Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone he) hd
-- Envelope
lemma buy : GaugeLocal S (youth F Y) f! :=by
    obtain ⟨hg,hj,hB⟩:=informed F X Y J W μ g q.extendsX
    refine ⟨?_,fun v ht U=> ?_,fun U V hP=>?_⟩
    · let f' A:=noiseTaylor S W A i; let p:Config G f→ Config G c:=fun U=> S.prediction U i; let s (Q:Config G c):= S.kernel.penalty * ∑ j,G.price ((represent (tint G (Exterior.Body 1 c) x)) j*(Q j)⁻¹)
      have he:Continuous s:=by unfold s; fun_prop
      obtain ⟨b,hB⟩:= (isCompact_range he.norm|>.bddAbove)
      unfold rental; simp_rw [sub_eq_add_neg]; exact (backdrop (R.exponentEnv sold) hg).add (((RG.Envelope.const _).mul (backdrop (backdrop (show RG.Envelope s from ⟨he.measurable,b,fun i=>hB ⟨i,rfl⟩⟩) (S.prediction_meas hD i)) hg)).neg)
    · unfold rental; rw [invites F X Y J W μ g q.extendsX v ht]
    unfold rental; rw [hB U V hP]
end Posture
end YM.MSbar.Heath.Cottage
