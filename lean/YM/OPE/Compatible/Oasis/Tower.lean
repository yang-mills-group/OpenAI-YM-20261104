import YM.OPE.Compatible.Oasis.Wick
/-! # One pulse. Threshold contraction independent of total parent trace. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
open Lass Lass.Zest MatchZ
open Source Labels
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}{k k' l j:ℕ}{T:Stage}
lemma nativeG {h:ℝ→Prop}(p:∀ f:ℕ→ℝ,Tendsto f atTop atTop → ∀ᶠ i:ℕ in atTop,h (f i)):∀ᶠ i:ℝ in atTop,h i:=by
       by_contra hX; have hp:∃ᶠ i:ℝ in atTop,¬ h i:=by simpa only [Filter.Frequently, not_not] using hX
       choose f hf hQ using fun i:ℕ=> frequently_atTop.mp hp (i:ℝ); obtain ⟨k,hk⟩:= (p f (tendsto_atTop_mono hf tendsto_natCast_atTop_atTop)).exists; exact hQ _ hk
open Hark
noncomputable abbrev ages (p:ℝ)(β:ℝ):ℝ:= Real.exp (p*Real.log β)
section
variable (a:Stage)(k:ℕ){A:Labels.Frame G l} (S:SectionData A) (H:Hol G)
include S in
lemma coastReady : ∀ᶠ x:ℝ in atTop,∀ (U:BudgetPoint)(b:ℝ),Tag a x U b → Widen U (fieldQ S x):=by -- n unused
       have ht :∀ᶠ x:ℝ in atTop, θj x*(1+(fieldQ S x:ℝ))^a.power≤1:=by
             let p:ℝ→ℝ:=id; have hb:= ((Score.steady (1:ℝ) (carth (show Tendsto p atTop atTop from tendsto_id))).plus (fieldReading A S tendsto_id) (carth (show Tendsto p atTop atTop from tendsto_id))|>.power a.power (carth (show Tendsto p atTop atTop from tendsto_id)))
             exact (((edgeθ (β:=p) tendsto_id).pays (carth (show Tendsto p atTop atTop from tendsto_id)) |>.mul (waitG (show Tendsto p atTop atTop from tendsto_id) hb)).tends (by norm_num) (carth (show Tendsto p atTop atTop from tendsto_id))).eventually (ge_mem_nhds zero_lt_one)
       filter_upwards [ht] with x hx U b hh; unfold Widen; rw[hh.tax,hh.scale]; exact hx
lemma term_acquire (hk:k+6≤ a.order)(he:S.Sound H): ∀ᶠ x:ℝ in atTop,∃ p:ℕ,∀ (n:Side), p ≤ n.val → ∀ (Q:Rep G n)(P:A.Coeff → Coefficient A n), Registered x a H Q S P→∃ P₁:Torch S H 0 Q P k (salary x),Grant (z:=x) P₁ a:=by
       refine (coastReady a S).mono (fun x hx=>⟨Θsize (fieldQ S x),fun n hn Q P hp=> pointR hp he (hx _ _ hp.TagQ) hn hk⟩)
end
end YM.OPE.CardinalQ
