import YM.RGComparison01.Marks.Trees
import YM.RGComparison01.Marks.Aurora
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
local notation "bZ" => H.birth
local notation "TZ" => Tree.Forest S.ratio
/-!
# First unmasked part of connected marked OUTPUT

 Keep real induction derivatives on ALL clustering lengths even with
 rough inherited e. Size is BEFORE reclosure/coupling reset; Kernel
 projection to be proven with full gas partners. -/
namespace Pillow
open Baked Palette March OmitClusters Next.Foundations
variable (M:ι→Leaf R)(ρ : ι→ℝ)
abbrev Tags := (Tickets (Palette.sign M S))
-- amplitude recorded EXPLICIT, no negative norms. thresholds relative.
def divAmt (p:Tags M (S:=S)) := ∏ i∈ p.val, ρ i
def part (χ:Chi)(p:Cake M H)(V:Config G c):= (divAmt M ρ p.2) * Team.driver (Palette.team M p.2) χ Q.table p.1.val Q.halo T W s o.K o.a V
-- sign of exponent ADD inside Mark.Poly not minus
abbrev glass (χ:Chi)(p:Baked.Cl M H)(V:Config G c):= Gas.term (Baked.seam M H) (fun i=>part M ρ χ i V) p
abbrev emberP (χ:Chi)(p:Cake M H)(V:Config G c):= divAmt M ρ p.2*((Palette.team M p.2).lotus T s χ o.K W o.a Q.table Q.halo V p.1.val)
abbrev pottery (χ:Chi)(p:Baked.Cl M H)(V:Config G c):= Gas.term (Baked.seam M H) (fun i=>emberP M ρ χ i V) p

/-- Carry invoice with paying directions at rooted support.Price compatibility. -/
structure Knot (Ω:Utopia H j v d r C' χ)(e B a t c q :ℝ)(k:ℕ) : Prop extends Range Ω e B a t k where
   payScale : c ≥ Pressure.temp s
   positive : 0<v
   income : 0 ≤ q
   earns : Sailor G c q j
   near : j*q ≤ v
-- have film
variable (U:Knot Ω e B a t A D k) (he:Casing R x Ψ)
local notation "La" => maskRaise Ω Ψ x e
variable (hr : ∀ i:ι,0≤ ρ i)
include hr he U
lemma film (p:Cake M H) : LocalOn (raised M H p) (part M ρ χ p) ∧ Measurable (part M ρ χ p) ∧ GaugeInvariant (part M ρ χ p) ∧
    emberP M ρ χ p=masked (Pressure.temp s) (raised M H p) (part M ρ χ p) ∧
    ∀ V,Healthy (Pressure.temp s) (raised M H p) V → Ore V (part M ρ χ p) v (glaze M ρ Ω k B (La) p) j := by
  have hh:= Team.qlocalFbb_debtor (Palette.team M p.2) H U.toRange he p.1.2.2 U.positive.le -- includes hp
  let a:= divAmt M ρ p.2; have ha:0≤a := prod_nonneg fun i _=> hr i; let zH:= raised M H p
  unfold part
  refine ⟨fun i j hx=>congr_arg (_*·) (hh.1 i j hx), measurable_const.mul hh.2.1, fun k V=> congr_arg (_*·) (hh.2.2.1 k V),funext (fun i=>?_),fun V hx E _ _ _ V' x r hp=>?_⟩
  · unfold emberP; rw [congr_fun hh.2.2.2.1 i]
    by_cases ht : Healthy (Pressure.temp s) zH i
    · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (show Healthy _ (H.unionP p.1.1) _ from ht)]
    rw [masked_ne _ _ _ _ ht, masked_ne _ _ _ _ (show ¬ Healthy _ (H.unionP p.1.1) _ from ht),mul_zero]
  have he := ((hh.2.2.2.2 _ hx) E V' x r hp).smul a; rw [Real.norm_of_nonneg ha] at he; exact he
-- funding shape for connected log
lemma process (p:Baked.Cl M H) : LocalOn (origins M H p) (glass M ρ χ p) ∧ Measurable (glass M ρ χ p) ∧ GaugeInvariant (glass M ρ χ p) ∧
    pottery M ρ χ p=masked (Pressure.temp s) (origins M H p) (glass M ρ χ p) ∧
    ∀ V,Healthy (Pressure.temp s) (origins M H p) V → Ore V (glass M ρ χ p) v (debt M ρ Ω p k B (La)) j:= by
   let v i:= part M ρ χ (p.2 i); have hf i:= film M ρ U he hr (p.2 i); let Z := origins M H p
   let Y i:= raised M H (p.2 i); have hh i:Y i⊆Z:=subset_biUnion_of_mem (raised M H ∘ p.2) (mem_univ _)
   let c:=coefficient (seam M H) p.2
   let b:ℝ:= c/(p.1+1).factorial
   have ha:glass M ρ χ p=fun V=> b*∏ i,v i V:=funext fun V=>by unfold glass Gas.term; unfold b c v; ring
   have hc:pottery M ρ χ p=fun V=> b*∏ i,masked (Pressure.temp s) (Y i) (v i) V:=by
     ext1 i; unfold pottery Gas.term; dsimp only; rw [prod_congr rfl (fun j (_:j∈univ)=> (congr_fun ((hf j).2.2.2.1) i))]; unfold b c Y v; ring
   rw [ha,hc]
   refine ⟨fun V U h=>?_ ,measurable_const.mul (measurable_fun_prod _ (fun i _=> (hf i).2.1)),fun u V=> ?_,funext (fun V=>?_),fun V hx E _ _ _ f x h hm=>?_⟩
   · exact congr_arg (fun x=> b*x) (prod_congr rfl fun i _=> (hf i).1 V U (agrees_mono h (coe_subset.mpr (hh i))))
   · exact congr_arg (fun x=> b*x) (prod_congr rfl fun i _=> (hf i).2.2.1 u V)
   · by_cases h:Healthy (Pressure.temp s) Z V
     · rw [masked_eq _ _ _ _ h]; exact congr_arg (fun x=> b*x) (prod_congr rfl fun i _=> masked_eq _ _ _ _ (show Healthy (Pressure.temp s) (Y i) V from Finset.disjoint_of_subset_left (hh i) h))
     rw [masked_ne _ _ _ _ h]; obtain ⟨x,h,hp⟩:=not_disjoint_iff.mp h
     obtain ⟨i,hi,hx⟩:=mem_biUnion.mp h
     rw [prod_eq_zero hi (masked_ne _ _ _ _ (Finset.not_disjoint_iff.mpr ⟨x,(show x∈ Y i from hx),hp⟩)),mul_zero]
   let g i:= glaze M ρ Ω k B (La) (p.2 i)
   have hk:=(Brush.all_prod univ (fun i x=> v i (f x)) g (fun _=>1) (fun i _=> (hf i).2.2.2.2 V (Finset.disjoint_of_subset_left (hh i) hx) E f x h hm)).trim; apply (hk.smul b).climb _ le_rfl
   simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]; unfold debt clusters; change ‖b‖*((∏ i,g i)*(1+((p.fst+1:ℕ):ℝ))^j) ≤ |c| * (∏ i,2^j*g i)/_
   conv_rhs => rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
   have h₁ : (1+((p.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(p.fst+1) := by
     rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=p.fst+1)
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ (show 0≤∏ i,g i from prod_nonneg fun i _=>zero_glaze M ρ Ω (p.2 i) U.paidB he U.paidE hr)) (norm_nonneg b)).trans_eq ?_
   unfold b; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ ((p.1+1).factorial:ℝ))]; ring

abbrev RegDebt (p:Baked.Cl M H) (Ω:Utopia H j v d r C' χ)(k n:ℕ)(B:ℝ)(b:Head S→ℝ):=(shiftG s*(1+coverNumber (radiusB s) (origins M H p)))^(n*j)*debt M ρ Ω p k B b
lemma pride (p:Baked.Cl M H) (P:BudgetPoint) (hp : P.threshold=Pressure.temp s)(hk : P.order ≤ j)(hn : P.power ≤ n) : pottery M ρ χ p=masked P.threshold (origins M H p) (glass M ρ χ p) ∧ P.Regular (origins M H p) (glass M ρ χ p) ∧ ∀ x'∈origins M H p,P.supBounds x' (origins M H p) (glass M ρ χ p) (RegDebt M ρ p Ω k n B (La)):= by
  let Z:=origins M H p
  obtain ⟨hx,hY,hF,hz,h⟩:= process M ρ U he hr p
  have hL V (hh : Healthy P.threshold Z V) : Ore V (glass M ρ χ p) v (debt M ρ Ω p k B (La)) j:= h V (hp ▸ hh)
  have hh (V) (ht : Healthy P.threshold Z V) : ContDiffAt ℝ (↑P.order) ((glass M ρ χ p) ∘ increment V) 0 := (charted (hL V ht) U.positive).of_le (Nat.cast_le.mpr hk)
  have ha : Sailor G P.threshold D j := ⟨fun c _ hb => U.earns.stroke c _ (hb.trans (hp.trans_le U.payScale))⟩
  refine ⟨(by rw [hp]; exact hz),⟨hx,hY,hF,hh,fun V hV A l hl=> left_has A hl (hh V hV)⟩,fun x' hv=>?_⟩
  let D := radiusB s; let b:ℝ := coverNumber D Z; let Y':= shiftG s*(1+b)
  have ht : 0≤ b := Nat.cast_nonneg _
  have hi : 1≤Y' := one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB s)]) (le_add_of_nonneg_right ht)
  have hp := grain (k:=k) M ρ Ω p U.paidB he U.paidE hr
  refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans hi) _) hp,fun V hV l hl hq=>?_⟩
  apply (costsD (g:=glass M ρ χ p) hx ha U.income x' _ U.near (hL V hV) (Y:=Y') ?_ hi l (hl.trans hk) hq).trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hi (Nat.mul_le_mul_right j hn)) hp))
  intro y hy; have hf : (separation y x':ℝ) ≤ b*(4*(D:ℝ)+2)+2*(D:ℝ) := by unfold b; exact_mod_cast Corona.extent Z D hy hv
  unfold Y' shiftG; change _≤ 4*(2*(D:ℝ)+1)*(1+b); nlinarith [Nat.cast_nonneg (α:=ℝ) D]
lemma brocade {m' h δ:ℝ} (_hh: 0 ≤ m')(hV:0<δ) {w:Cake M H→ℝ} (hw:∀ i,0≤w i)
    (hK:Ac.Hit (origins M H) (radiusB s) (fun p=> Baked.weight M w p * debt M ρ Ω p k B (La)) (m'+δ) h) :
    Ac.Hit (origins M H) (radiusB s) (fun p=> Baked.weight M w p * RegDebt M ρ p Ω k n B (La)) m' (collars G δ s j n * h) := by
   intro x'
   have he' : 0 ≤ shiftG s := by unfold shiftG; positivity
   have hv : 0 ≤ collars G δ s j n := by
     unfold collars Reserves.polyPrice; positivity
   have hb := budget_scale hv (hK x')
   refine budget_mono hb (fun z => ?_) (fun z => ?_)
   · split; next => exact mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> hw _) (mul_nonneg (pow_nonneg (mul_nonneg he' (add_nonneg zero_le_one (Nat.cast_nonneg _))) _) (grain M ρ Ω z U.paidB he U.paidE hr))) (Real.exp_nonneg _)
     next => exact le_rfl
   dsimp only; split; next hx =>
      let c0 : ℝ := coverNumber (radiusB s) (origins M H z)
      have hc0 : 0 ≤ c0 := Nat.cast_nonneg _
      have Hc : (1+c0)^(n*j) ≤ polyPrice δ (n*j) * Real.exp (δ*c0) := polynomial_cost hV hc0 _
      let Y := debt M ρ Ω z k B (La); have hD: 0 ≤ Y:= grain M ρ Ω z U.paidB he U.paidE hr
      change Baked.weight M w z * ((shiftG s*(1+c0))^(n*j) * Y) * Real.exp (m'*c0) ≤ _*(_ * Real.exp ((m'+δ)*c0)); rw [mul_pow]
      refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hc (pow_nonneg he' _)) hD) (show 0 ≤ Baked.weight M w z from prod_nonneg fun _ _=> hw _)) (Real.exp_nonneg (m'*c0))) ?_
      rw [add_mul,Real.exp_add]; unfold collars; apply le_of_eq; ring
   next=> rw [mul_zero]
end Pillow
end YM.RGComparison01.Pledge
