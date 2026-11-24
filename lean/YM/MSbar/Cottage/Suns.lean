import YM.MSbar.Cottage.Cradle
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
def woolModel (R:Rep G f)(Y:Support f)(i:S.Choices)(Q:Config G c)(μ:Positions (Key F G))(A B:ℝ)(U:Config G f) :=
    let g := fun U:Config G f=> spec (hotel F X Y J Q μ A B) U*Real.exp (rental F J R Y i Q μ U)
    g U/(∫ t:IV F (board F X) G,g (twirl F (board F X) t U)∂fence F (board F X) G)
local notation "m!"=> woolModel F X J R Y i W μ A B
namespace Posture
variable (sold:R.Lawful σ C T δ w)(hD:S.patch.Branches S.kernel G)(hB: Decent R.clip R.p)(hz:0≤ R.beta)
variable {p J F X Y x μ i}
include q g h sold hD hB hz
lemma harvest (hr:r≤1)(hu : gardenCity p J K r B) : 
    Rota R W (youth F Y) F (board F X) (hotel F X Y J W μ A B) (woolModel F X J R Y i W μ A B) (Real.exp (wSize G R.p σ C δ T R.beta M Y.card X.card p K B)/moss G r (board F X).card) (Real.exp (silkRoad C σ δ T R.beta X.card M R.p k)) :=by
    let Y':=Y!; let Z(U):=spec Y' U *Real.exp (f! U); let I:=board F X; let x':= youth F Y; let μ':= fence F I G
    let P(U):=∫ t,Z (twirl F I t U)∂μ'; have hp: m! = Z/P:=rfl
    let b:=wSize G R.p σ C δ T R.beta M Y.card X.card p K B; let a:=moss G r I.card; have hr':= hu.1; have ha : 0 < a:=by unfold a moss; positivity
    have hN:= buy i h g q sold hD hB hz; let H':Seal S x' Y':= garden_main F X Y J W μ g q.extendsX
    have hZ: GaugeLocal S x' Z := gaugeMoney (specReady _ H') (show GaugeLocal _ x' (fun U=> Real.exp (f! U)) from ⟨ hN.currency.exp,fun i he U=> congr_arg Real.exp (hN.turn i he U),fun U V H=> congr_arg Real.exp (hN.located U V H)⟩)
    have hT(i:IV F I G) : GaugeLocal S x' (fun U=> Z (twirl F I i U)):= twisted F I Z hZ i (hedge F X Y J g q.extendsX i)
    have hP : GaugeLocal (G:=G) S x' P := by
       refine ⟨?_,fun i he U=>integral_congr_ae (Eventually.of_forall (fun t=> (hT t).turn i he U)),fun U V hv=>integral_congr_ae (Eventually.of_forall (fun t=> (hT t).located U V hv))⟩
       exact unroll (f:=fun p:Config G f× IV F I G=> Z (twirl F I p.2 p.1)) (μ:=μ') (backdrop hZ.currency ((twirlD F I G).comp (continuous_snd.prodMk continuous_fst)|>.measurable))
    have hP₁(i)(t:IV F I G):P (twirl F I t i)=P i:=by
       unfold P;simp_rw [ends]; exact (climber F I G t).integral_comp (Homeomorph.mulRight t).measurableEmbedding (fun t=> Z (twirl F I t i))
    have hP' (j₀:Config G f)(hi: j₀∈ hotel F X Y J W μ A B) : P j₀ ≥ Real.exp (-b)*Z j₀ *a:=by
       let S':Set (IV F I G):= (fun t=> twirl F I t j₀)⁻¹' Y'; let mG(t):=Z (twirl F I t j₀); let E:= S'.indicator (fun _=> Real.exp (-b)*Z j₀); let u:= Z j₀; have hn : u= Real.exp (f! j₀) :=by unfold u Z; rw [show spec Y' j₀=1 from Set.indicator_of_mem hi _,one_mul]; -- notation j₀ collision.H!
       have hF(t:IV F I G): E t ≤ Z (twirl F I t j₀):= by
           by_cases h₀:t∈S'
           · rw [show E t= Real.exp (-b)* Z j₀ from Set.indicator_of_mem h₀ _, (show Z j₀= Real.exp _ from hn)]
             unfold Z; rw [show spec Y' (twirl F I t j₀)=1 from Set.indicator_of_mem (show twirl F I t j₀∈ Y' from h₀) _,one_mul,← Real.exp_add]; apply Real.exp_monotone; linarith only [(abs_le.mp (clover i h ‹Clear ..› q sold hB hz t hi h₀)).1]
           rw [show E t=0 from Set.indicator_of_notMem h₀ _]; exact mul_nonneg (Set.indicator_nonneg (fun _ _=>zero_le_one) _) (Real.exp_pos _).le
       have hs : MeasurableSet S':= H'.from_here.preimage (((twirlD F I G).comp (continuous_id.prodMk continuous_const)).measurable); have hg: RG.Envelope mG:=backdrop hZ.currency (((twirlD F I G).comp (continuous_id.prodMk continuous_const)).measurable)
       have hv:= spruces ‹Clear ..› q hi hr hu
       change _ ≤ μ'.real S' at hv; have hk: (∫ x,E x ∂μ')= Real.exp (-b)*Z j₀*μ'.real S':=by unfold E; rw [integral_indicator hs,setIntegral_const, smul_eq_mul,mul_comm]
       refine (mul_le_mul_of_nonneg_left hv (mul_nonneg (Real.exp_pos _).le ?_)).trans (hk.ge.trans (integral_mono (Integrable.indicator (integrable_const (μ:=μ') _) hs) (hg.integrable _) hF)); exact (Real.exp_pos _).le.trans_eq hn.symm
    have hl(j): 0≤ Z j:= mul_nonneg (Set.indicator_nonneg (fun _ _=>zero_le_one) _) (Real.exp_pos _).le
    have he := silkRoad C σ δ T R.beta X.card M R.p k
    have hR:0 ≤ m! := fun i=> div_nonneg (hl i) (integral_nonneg (fun t=> hl _))
    have ht₀(U)(ht:U∈Y'): Z U=Real.exp (f! U):=by unfold Z; rw [show spec Y' U=1 from Set.indicator_of_mem ht _,one_mul]
    have ht₁(U)(ht:U∉Y'): Z U=0:=by unfold Z; rw [show spec Y' U=0 from Set.indicator_of_notMem ht _,zero_mul]
    have hW(U)(ht:U∉Y'): m! U=0:=by change Z U/P U=0; rw [ht₁ U ht,zero_div]
    have hU(U)(ht:U∈Y'):0<P U:=lt_of_lt_of_le (mul_pos (mul_pos (Real.exp_pos _) (by rw [ht₀ U ht]; exact Real.exp_pos _)) ha) (hP' U ht)
    have hm(U:Config G f): m! U ≤ Real.exp b/a:=by
       by_cases hh:U∈Y'
       · change Z U/P U ≤ _; apply (div_le_div_iff₀ (hU U hh) ha).2; apply le_trans _ (mul_le_mul_of_nonneg_left (hP' U hh) (Real.exp_pos _).le); rw [Real.exp_neg]; exact le_of_eq (by field_simp)
       rw [hW U hh]; positivity
    refine ⟨H',fun t=>hedge F X Y J g q.extendsX t,⟨⟨ hZ.currency.meas.div hP.currency.meas, Real.exp b/a,fun i=> (Real.norm_of_nonneg (show 0 ≤ m! i from hR i)).trans_le (hm i)⟩,fun t hv i=> congr_arg₂ (·/·) (hZ.turn t hv i) (hP.turn t hv i),fun U V h=> congr_arg₂ (·/·) (hZ.located U V h) (hP.located U V h)⟩,fun t U h₀ h₁=> dues g q t h₀ h₁,hR,hm,hW,?_,?_⟩ -- ht used
    · intro t U hc hC; have hp:=charge i h g q sold hD hB hz t hc hC -- signature
      let V:=twirl F I t U

      change S.density R.beta U W * (Z V/P V)* Real.exp (R.exponent U-R.exponent V) ≤ Real.exp (silkRoad C σ δ T R.beta X.card M R.p k) * (S.density R.beta V W * (Z U/P U))
      rw [hP₁ U t,ht₀ U hc,ht₀ V hC] -- V notation.
      rw [← mul_div_assoc,div_mul_eq_mul_div,← mul_div_assoc, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hp (hU _ hc|>.le)
    intro U hV; unfold woolModel; change (∫ t: IV F I G,Z _ / P (twirl F I t U)∂ μ')=1; simp_rw [hP₁]; rw [integral_div,show (∫ i,Z _∂ μ')=P U from rfl, div_self (hU U hV).ne']
end Posture
end YM.MSbar.Heath.Cottage
