import YM.LocalLTE.East.Lantern
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open Scarf Refrain Marlin Opera
variable {ε :ℝ}
variable (P:BudgetPoint)(χ:Chi) (p:ℝ)
lemma tory (Q:Magazine H→ Config G c→ℝ) (hq:∀ (i:Songbook c),Q (.inr i)=0)(hp:Meadow.Budget P (Beam.dashboard H) (Q ∘ Sum.inl) p): Meadow.Budget P ((Beam.marquee H P).reg) (Song.choir Q ∘ pennant H) (turnFee P*p):=by
   obtain ⟨f,h,hp⟩:= hp; apply Meadow.soared
   refine ⟨Sum.elim f 0,fun i=>?_,fun i=>?_⟩; swap
   · rcases i with i|i; exact hp _; rw [hq]; exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) abs_zero.le⟩
   rw [← add_zero p]
   apply Cost.sum
   · exact h i
   simp [SumBudget]
def surveyH (q:H.fragrances→Prop) : Magazine H→ Config G c→ℝ:= Sum.elim (fun i=> if q i then sequence H (Meadow.intern H) χ i else 0) (fun _=> 0)
def visor (q:H.fragrances→Prop) : ℕ→ Config G c→ℝ:= choir (surveyH H χ q) ∘ pennant H
lemma voiced (q:H.fragrances→Prop) (D:ℕ→ℝ)(hp:∀ i,1≤ D i)(hv: Voices H P χ p D)(a:ℝ) (ha:0<a)(h:∀ i,q i→ Height.ancestry i ∧ a ≤Height.rocket H D i): Meadow.Budget P ((Beam.marquee H P).reg) (East.visor H χ q) (turnFee P*(a⁻¹*p)):= East.tory H P _ (East.surveyH H χ q) (fun _=>rfl) (riseBirth H P χ p q D hp hv a ha h)
lemma cultured (v:ℕ→ℝ)(hp:∀ i,1≤v i)(hr:Voices H P χ p v)(γ:ℝ): Meadow.Budget P ((Beam.marquee H P).reg) (Meadow.heats H χ γ) (turnFee P*p):=by
   have hz:= voiced H P χ p Height.ancestry v hp hr 1 zero_lt_one (fun i h=>⟨h,East.toll H _ hp i⟩); rw [inv_one,one_mul] at hz; exact hz

variable {C d u Y' B' q' M' A' r' a' :ℝ}
variable (K':Captain H j C d u Y' B' q' M' A' r' m χ) (hx:P.order≤j) (hg:P.power≤n)(hB:P.B=radiusB s) (hV:P.threshold=Pressure.temp s)(hR:preExponent P ≤ a')
    (h : Ac.Hit (Captain.reachability (H:=H)) P.B (fun i=> if Height.tiredN H ℓ i then K'.markΦ i n else 0) a' p)
include K' hx hg h hV hR
lemma cloudPrice {Q:H.fragrances→Prop} (hp:∀ i,Q i→∀ V: Config G c,stream H χ V i≠ 0→Height.tiredN H ℓ i) : Meadow.Budget P ((Beam.marquee H P).reg) (East.visor H χ Q) (turnFee P*p):=by
    refine East.tory H P p (East.surveyH H χ Q) (fun _=>rfl) ?_
    let f i:= if Height.tiredN H ℓ i then K'.markΦ i n else 0
    have h' i :0≤ f i:=by
      unfold f; split; next => exact (K'.gloryBudget _ _ hV hx|>.2.2 n hg (Beam.dashboard H i).site ((show (Beam.dashboard H i).support=Captain.reachability i from Beam.see ..) ▸ (Beam.dashboard H i).anchor)).1
      exact le_rfl
    refine ⟨f,fun x=>budget_mono (h x) (fun i=>?_) (fun i=>?_),fun i=>?_⟩
    · split; next => exact mul_nonneg (h' _) (Real.exp_nonneg _)
      exact le_rfl
    · dsimp only; split
      next hi =>
        have he:(Beam.dashboard H i).support=Captain.reachability i:= Beam.see H i
        rw [if_pos (show x∈Captain.reachability i from hi ▸ he ▸ (Beam.dashboard H i).anchor),he]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _))) (h' _)
      exact (h x).1 i
    have hz:P.Regular (Beam.dashboard H i).support (0:Config G c→ℝ) ∧ P.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (0:Config G c→ℝ) (f i):= ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const 0) (abs_zero.trans_le (h' i))⟩
    unfold East.surveyH; dsimp only [Function.comp_apply,Sum.elim]; split
    next hi=>
      by_cases he:Height.tiredN H ℓ i
      swap; · rw [Song.sequence,Meadow.coincides,show (fun V=> stream H χ V i)=(0:Config G c→ℝ) from funext (fun V=> not_not.mp fun hV=>he (hp i hi V hV)),smul_zero]; exact hz
      have hL:= K'.gloryBudget i _ hV hx
      have hU:=(CouplingShape.sup_scale (-1) (hL.2.2 n hg (Beam.dashboard H i).site ((show (Beam.dashboard H i).support=Captain.reachability i from Beam.see ..) ▸ (Beam.dashboard H i).anchor))); rw [abs_neg,abs_one,one_mul] at hU
      unfold f; rw [if_pos he,Song.sequence,Meadow.coincides,Beam.see]; exact ⟨CouplingShape.reg_scale _ (hL.2.1),hU⟩
    exact hz
end YM.PhysicalNext.Repeat.East
