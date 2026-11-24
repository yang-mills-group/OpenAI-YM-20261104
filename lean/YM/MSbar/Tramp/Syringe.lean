import YM.MSbar.Tramp.Pedal
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge)(n: Side)
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "X"=>Positions (Cards G n)
local notation "T"=> cards0 G n
local notation "H"=>cardsH G n
local notation "U"=> slide G n
local notation "L"=> Measuring.chart n G
variable (x:Primary n G)(v:Positions (Cards G n))(p:ℕ)
lemma solid1 : ‖cards0 G n v‖≤‖v‖:=by apply pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr; intro i; exact norm_le_pi_norm v (Sum.inl i)
lemma pin (i:Primary n G)(x: Π!): ‖tune i x‖ ≤ shade G*‖x‖:= (norm_le_pi_norm ((tint G _) x) i.1).trans (tint_le _)
lemma mild (y:Site n): ‖cardsH G n v y‖≤ shade G*‖v‖:=by
    let W:=cardsL G n; have he : ‖W v‖≤‖v‖:=by refine pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr fun i=> ?_ ; exact norm_le_pi_norm v (.inr (.inl i))
    exact (norm_le_pi_norm ((tint G _) (W v)) y).trans ((tint_le _).trans (mul_le_mul_of_nonneg_left he (shade_pos ..|>.le)))
lemma launched : ‖launch G n x‖ ≤ shade G :=by
    apply ContinuousLinearMap.opNorm_le_bound _ (shade_pos ..|>.le)
    intro v; let V:=tune x (T v); change max ‖v (Sum.inr (Sum.inr x))‖ (max ‖V‖ (max ‖H v _‖ ‖H v _‖)) ≤ _
    exact max_le ((norm_le_pi_norm v _).trans (le_mul_of_one_le_left (norm_nonneg _) (shade_one G))) (max_le ((pin ..).trans (mul_le_mul_of_nonneg_left (solid1 ..) (shade_pos ..|>.le))) (max_le (mild ..) (mild ..)))
lemma burnt : launch G n x (haul _ (curbL (slide G n) (Measuring.chart n G x) 1) v)= launch G n x v :=by
    let S:= curbL U (L x) 1; let z:= haul _ S v
    have hp(i:Cards G n) (he:separation (U i) (L x) ≤ 1): z i=v i:= by unfold z haul; rw [if_pos (show i∈ S from Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)]
    have h(i:Site n)(he:separation i (L x) ≤ 1): H z i=H v i:=by ext k; exact hp (.inr (.inl (i,k))) he
    apply Prod.ext; · exact hp (.inr (.inr x)) (by unfold slide; simp)
    apply Prod.ext
    · change tune x (T z)= tune x (T v); ext i; exact hp (.inl (x.1,i)) (by unfold slide; simp [Measuring.chart])
    apply Prod.ext; · exact h _ (by change separation (L x) _ ≤ _; simp)
    exact h _ ((separation_comm ..).trans_le (Work.E01.sep_step_le ..))
noncomputable def favor (G:Gauge)(p q:ℕ) :=(∑ j:G.ColorIndex, ‖iteratedFDeriv ℝ q (ventral G p j) 0‖) * (shade G)^q
lemma ruby (q:ℕ): Lumber (slide G n) (Measuring.chart n G x) 1 (clue (auroraS G n p x)) q (favor G p (q+1)):=by
    rw [funext (sprite G n p x)]
    refine native (iridesce G n p) x q U _ _ _ ((spell ..).contDiffAt.of_le le_top) ?_ (Eventually.of_forall fun y=>?_)
    · let V:= launch G n x; let L':=ventral G p x.2; rw [show iridesce G n p x=L' ∘ V from funext fun i=>flutter ..,V.iteratedFDeriv_comp_right (tints G p x.2) _ le_top,V.map_zero]; let f:= iteratedFDeriv ℝ (q+1) L' 0; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      let A₁:(G.ColorIndex) →ℝ:=fun j=> ‖iteratedFDeriv ℝ (q+1) (ventral G p j) 0‖; have hv:‖f‖≤ ∑ i,A₁ i:=Finset.single_le_sum (s:=Finset.univ) (f:=A₁) (fun _ _=>norm_nonneg _) (Finset.mem_univ x.2); apply mul_le_mul hv _ (by positivity) ((norm_nonneg _).trans hv); rw [Finset.prod_const]; simp only [Finset.card_univ,Fintype.card_fin]; exact pow_le_pow_left₀ (norm_nonneg _) (launched G n x) _ -- check lemma
    change iridesce _ _ _ _ _ = _; rw [flutter,burnt,flutter]
noncomputable def light (G:Gauge)(n:Side)(p:ℕ): Pot (Cards G n):=∑ i:Primary n G, auroraS G n p i
noncomputable def tub (G:Gauge)(a:ℝ)(s p m:ℕ):ℝ:=∑ q∈Finset.range (m+1), cities (tintCost G) 1 * rugL a (favor G p (q+1)) s 1 q (cities (summerSize G) 1)
lemma supported (a:ℝ)(s p m:ℕ)(ha:0≤a): Tokew (slide G n) a s m 0 (light G n p) (tub G a s p m):=by
    let C₁(i:ℕ):= (cities (tintCost G) 1:ℕ); let F(i:ℕ):ℝ:= (C₁ i:ℝ)*rugL a (favor G p (i+1)) s 1 i (cities (summerSize G) 1)
    have hZ(i:ℕ):0≤favor G p (i+1):=by unfold favor; have hx:=shade_pos G; positivity
    have hF(i:ℕ): 0≤F i :=by unfold F rugL; have he:=hZ i; have hp:=wpos a s (2*1); positivity
    refine (token _).mpr ⟨Finset.sum_nonneg (fun i _=> hF i),fun j hj i=> ?_⟩
    refine (logHome U ha L _ (fun x=>ruby G n x p j) (fun x=>dressP _ (tok1 G n) x _) (fun x=> dressP _ (starM G n) x _) (hZ _) i).trans (Finset.single_le_sum (f:=F) (fun j _=> hF j) (Finset.mem_range.mpr (by omega)))
end YM.MSbar.Tramp
