import YM.MSbar.Rolling.Melt
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
variable (J:ChartRatio G)(hJ:LocalRatio J) (n:ℕ)
variable (A:PowerSeries (Pot (Primary f G))) (F:ℝ → Config G f→ℝ) (u:ℕ)
variable (hc:Serves S G) (hp:Critical B p R ρ) (hq:ClassicalMatch B p q R T ρ)
variable (ht:Trend F A R p u)
noncomputable def shunt (S:StepData c f)(F:ℝ → Config G f → ℝ)(t:ℝ)(v:Config G c):=boxS S F t v/boxS S F t 1
noncomputable def colorCut (ρ:fieldDir G c 1→AxisChart G B): Nesting G c:=Rewind (song B i R p J A ρ) (0:Positions (Primary c G))
local notation "M"=>colorCut B i R p J A ρ
local notation "B'"=> boxS S F
local notation "g!"=> grainS B i R T p q J F
include ht
lemma toneG : Kind (song B i R p J A ρ):=by unfold Kind song; rw [PowerSeries.coeff_map, sugar _ (well B i J A ht.bond),map_zero]
open MvPolynomial Whisk
lemma lasts : Expanse (song B i R p J A ρ) 1 u:=by
    let f':= barbed B i J A
    have he(L: Z→ℝ)(v:ℕ)(hv:v≤2) : Expanse (splitV (singularity L v)) 1 u:=by
       let Q:= singularity L v; refine ⟨fun p hp=>?_⟩; change totalDegree (µ p (splitV Q))≤ _; by_cases he:p=0; subst p; rw [splitK]; simp
       rw [splitV, _root_.map_sub,PowerSeries.coeff_C_of_ne_zero he,sub_zero]; unfold Q singularity; rw [PowerSeries.coeff_mk]; exact (potsD ..).trans (by omega)
    have hE:Expanse f' 1 u:=by
        obtain ⟨ha⟩:=he (swung B J) 0 (by omega); obtain ⟨hb⟩:=he (pushChart B G i) 2 le_rfl; refine ⟨fun p hp=>?_⟩; simp only [f',barbed,_root_.map_add,_root_.map_sub,PowerSeries.coeff_map]; refine (totalDegree_add ..).trans (max_le ?_ ((clearD _ _).trans (ht.plane.profile _ hp))); rw [sub_eq_add_neg]; refine (totalDegree_add ..).trans (max_le (ha _ hp) ?_); rw [totalDegree_neg]; exact hb _ hp
    refine ⟨fun j hj=>?_⟩; unfold song; rw [PowerSeries.coeff_map]; exact (clearD ..).trans ((Whisk.cohorts (well B i J A ht.bond) hE).profile j hj)
lemma Price.polar (t:ℝ)(x: Positions (Primary c G)) : taste u (picture x (colorCut B i R p J A ρ)) t= taste u (picture x (song B i R p J A ρ)) t - taste u (picture 0 (song B i R p J A ρ)) t:=by
    let K':=song B i R p J A ρ
    unfold colorCut taste picture; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,PowerSeries.coeff_map,Rewind,PowerSeries.coeff_mk,rewind, map_sub,MvPolynomial.eval_C,mul_sub] -- inspect
variable (hK : Matrix.PosDef (Push.Uniform.block (priced B i p R) 0))
include hp hc hq hJ hK
lemma olden : ∀ᶠ t in Γ,t^(Fintype.card (Key B G)+1) ≤ boxS S F t (1:Config G c):=by
    let a:= exitS K J; have ha:0<a:=perk J hJ K hK
    let P:= song B i R p J A ρ; have ht' : Kind P:= toneG B i R p ρ J A F u ht -- charargs
    let Y':= yard 0 (E:=X); have hy:Price Y' 1 (fun t x=> taste u (picture x (Spring P)) t-1):=by
        refine ((Price.xunit Y').product (girth _ (payY X 0) (Spring P) u)).bounds ?_; filter_upwards [width] with t ⟨ht,he,hd⟩ x hy; change _ ≤ |t*Belt u (picture x (Spring P))|; apply le_trans _ (le_abs_self _); have hp := sauce (picture x (Spring P)) u ht.le he
        rw [show µ 0 (picture x _)=1 from (by unfold picture; rw [PowerSeries.coeff_map,covers ht',_root_.map_one])] at hp; exact hp
    have hh:Price Y' 1 (fun t x=> g! t x-1):=((thickets B i R T p q ρ J hJ 0 A F u hc hp hq ht hK|>.poorly (by omega : 1 ≤ u+1)).nsum hy).egress (Eventually.of_forall fun x y _=>by unfold P; ring)
    filter_upwards [width, hh.reach (1/2) (by norm_num) (by omega),(eventually_lt_nhds (half_pos ha)).filter_mono nhdsWithin_le_nhds] with t hx hL hu; let d:=Fintype.card (Key B G)
    have hJ : t^(d+1) ≤ t^d*(a/2):=by rw [pow_succ]; exact mul_le_mul_of_nonneg_left hu.le (pow_pos hx.1 _|>.le)
    apply hJ.trans; have hm:= (abs_le.mp ((hL 0 (by simp [Y',yard])).le)).1; have he: 1/2≤ g! t 0:=by linarith
    unfold grainS at he; rw [postcard,smul_zero,_root_.map_zero,link_one,show height c q T (0:X)=0 from ?_,Real.exp_zero,one_mul] at he; swap; · rw [height, (pierce B i R T p q ρ hc.branches ht.quiet hp hq).second,map_zero]; simp
    have hv:= (le_div_iff₀ (mul_pos (pow_pos hx.1 d) ha)).mp he; linarith only [hv]
lemma newT : Trend (shunt S F) (colorCut B i R p J A ρ) T q u:=by
    let P:= song B i R p J A ρ; have ht' : Kind P:=toneG B i R p ρ J A F u ht
    have hp₀:=pierce B i R T p q ρ hc.branches ht.quiet hp hq; let S':=shunt S F
    refine ⟨hush ht',?_, ?_,?_, hp₀, ?_⟩
    · refine ⟨fun j hj=>?_⟩; have he:=(lasts B i R p ρ J A F u ht).profile j hj; unfold colorCut; rw [Rewind,PowerSeries.coeff_mk,rewind,sub_eq_add_neg]; refine (totalDegree_add ..).trans (max_le he ?_); rw [totalDegree_neg,totalDegree_C];omega
    · filter_upwards [ht.base] with t ⟨he,h₀⟩; obtain ⟨hp,hT,hE,hF⟩:=tipT (b:=t⁻¹^2) _ hc he; let p:=boxS S F t; have hx(x):0<p x:=hF x; have ht : p 1≠0:=(hx 1).ne'; refine ⟨⟨fun s U=>congr_arg (·/p 1) (hp s U),fun U s b=>congr_arg (·/p 1) (hT U s b),?_,fun U=>div_pos (hx U) (hx _)⟩,div_self ht⟩
      rw [show shunt S F t = fun v=>p v*(p 1)⁻¹ from funext fun j=> div_eq_mul_inv ..]; exact (hE.mul (Envelope.const _))
    · obtain ⟨L,a,ha,H⟩:=ht.control
      obtain ⟨b,hb,hS⟩:= shed S a ha G; let d:=Fintype.card (Key B G)
      let κ:=(1+b)⁻¹; have hV:0<κ:=inv_pos.mpr (by linarith); refine ⟨L+(d+1),κ,hV,?_⟩
      filter_upwards [ht.base, H, width,olden B i R T p q ρ J hJ A F u hc hp hq ht hK] with t hh ht hv he U
      let G':= boxS S F t; unfold shunt; rw [pow_add, ← div_div]
      have hh : G' U≤ Real.exp (-κ*Wilson.energy U/t^2)/ t^L := rises (F t) hc hh.1 ha t hv.1 _ hV b (le_trans (mul_le_mul_of_nonneg_left (show b ≤ 1+b by linarith) hV.le) (le_of_eq (inv_mul_cancel₀ (show 1+b≠0 from (by linarith))))) L ht hS U
      exact div_le_div₀ (div_nonneg (Real.exp_pos _).le (pow_nonneg hv.1.le _)) hh (pow_pos hv.1 _) he
    intro n
    have he:Price (yard n) (u+1) (fun t x=> Real.log (g! t x)-taste u (picture x P) t):= unveil _ (payY X n) P u ht' (thickets B i R T p q ρ J hJ n A F u hc hp hq ht hK)
    refine (he.cut (he.inherits (fun x y=> (0:X)) (width.mono (fun t ⟨ht,he,hp⟩ x hh=>by unfold yard; rw [norm_zero]; positivity)))).egress ?_
    filter_upwards [ht.base,width] with t ht' he x hx; let b:= exitS K J; let k:=Fintype.card (Key B G); let hatB:=boxS S F t; have hB(x):0 < hatB x:=(tipT _ hc ht'.1).pos x; have hR:0 < t^k * exitS K J:= mul_pos (pow_pos he.1 _) (perk J hJ K hK)
    have hc'(x): Real.log (g! t x)= height c q T x+Real.log (hatB (postcard G c t x))-Real.log (t^k*b):=by unfold grainS; rw [Real.log_div (mul_pos (Real.exp_pos _) (hB _)|>.ne') hR.ne',Real.log_mul (Real.exp_pos _|>.ne') (hB _|>.ne'),Real.log_exp]
    simp_rw [hc',Price.polar B i R p ρ J A F u ht t x]; rw [show height c q T 0=0 from (by unfold height; rw [hp₀.second,map_zero]; simp), show postcard G c t 0=1 from (by simp [postcard])]; unfold shunt; rw [Real.log_div (hB _|>.ne') (hB _|>.ne')]; unfold P hatB; ring
end YM.MSbar.Rolling
