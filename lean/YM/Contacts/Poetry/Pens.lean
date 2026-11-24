import YM.Contacts.Poetry.Cue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
/-! Geometry.P. Conditional smoothing ingredients for pooling all complements of tiny compatibility. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Trio Boulevard
open Slide (Stars)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {d n₀ m₀ m k : ℕ}
section generic
variable {A:Side} {t v : ℕ} {u:Offer G c} {w: Offer G C} {z:Offer G A} {B:BudgetPoint}
def Override (h:A.val=c.val*t)(z:Offer G A)(u: Offer G c)(p : BudgetPoint) := ∀ (x:Site A) (V:Config G c), flags p.threshold V=∅ → z x ((normal (Deck.divides h) h).links V)=u ((splitter (Deck.divides h)) x) V
lemma filters (P:Trio.Offer G c) (h:Mirrors P) (i:Site c) (V:Config G c): P 0 (Lattice.translate i V)=P i V := by rw [← pull_one,h]; simp [Lattice.affine]
lemma chromatic {r : ℕ} (hA:2*(r+1)<A.val) (ht:A.val=c.val*t) (hu:Override ht z u B) (hv:A.val=C.val*v) (hw:Override hv z w B) (hp : Mirrors u) (hq:Mirrors w) (hX:LocalOn (neighbors r (0:Site A)) (z 0)) : Trio.Compatible u w B r := by
  intro p q U W hk hh hE; let v:= translate p U; let t:=translate q W; have hf:flags B.threshold v=∅:=by unfold v; rw [←pull_one]; exact Pane.tranquility _ hk ..
  have hh:flags B.threshold t=∅:=by unfold t; rw [←pull_one]; exact Pane.tranquility _ hh ..
  have hu:=hu 0 v hf; have hw:=hw 0 t hh; rw [map_zero] at hu hw
  rw [← filters u hp p U,← filters w hq q W, ← hu,← hw]; apply hX _ _ (Slide.readNear 0 hA ?_); rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; unfold v t; rw [Slide.increases,Slide.increases]; exact hE
end generic
section earnest
variable {D:Stars→Side}{w:ℕ} {P : Patch} {K : Teller G} {x a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
    {S:StepData c f} {T:Tube G S} {R : RG.Rep G f} (H : Cash W x a L₀ X o U T R) {χ : Chi}
local notation "Bz" => radiusB x
variable (n₀) (Ξ: Lecturer R m₀) (χ) (B:BudgetPoint)(k) (β γ: ℝ)
local notation "K₀" => Poetry.studio X.halo (radiusB x) m₀ n₀
-- intended model F ∀stars compatible & scales. `e` maximal studio envelope. `z` ornament.
variable (e z ℓ:ℕ)(fa:∀ i:Stars,Offer G (D i)) (Q:∀ i:Stars,(D i).val=2*(w+i.val))
local notation "u" => (arena H χ β γ)
local notation "Z'" => Beam.marquee H B
local notation "V₁" => (gallery H χ β γ)
local notation "R₀" => (Poetry.panel n₀ H Ξ k)
local notation "P" => (Poetry.barony n₀ H Ξ χ k β γ)
def windup (i:Site c) (V:Config G c):= ∑ x∈(Poetry.panel n₀ H Ξ k), Meadow.garnerAt H B i x *((Z').read V₁|>.regularOccurrence B x V)
-- mask of read. subtract model as committed on all periods.Assume diff at small period with omitted optional Δ(w shifts). keep pressure floors.Affine-null paid separately.
def sore (m:Offer G c)(d:ℕ)(i: Site c) (V:Config G c):ℝ:= Poetry.windup n₀ k H χ Ξ B β γ i V - masked B.threshold (neighbors d i) (m i) V - ((P)-m) i 1 - Trio.unearned B Q z (rip fa) i V -- order inspect

variable (F₀:Offer G c)(t₀:ℕ){s t:ℝ}(htw:Collection.Local (Beam.marquee H B) B (gallery H χ β γ) s t)(hB:B.B=radiusB x)(hf: Trio.Mirrors F₀)
include hf htw
lemma rebid (V : Config G c): (Z'|>.read (V₁)|>.additive B V)=(Z'|>.read (timbres n₀ H χ Ξ β γ k)|>.additive B V) + (Fintype.card (Site c):ℝ)*((P)-F₀) 0 1 + (∑ i:Site c, masked B.threshold (neighbors z i) (ornament Q fa i) V) + (∑ i:Site c,masked B.threshold (neighbors t₀ i) (F₀ i) V)+∑ i,sore n₀ k H χ Ξ B β γ z fa Q F₀ t₀ i V := by
  have hp (i:Site c): ((P)-F₀) i (1:Config G c)= ((P)-F₀) 0 1:= by
    simp only [Pi.sub_apply]; rw [show i= Lattice.affine 1 i (0:Site c) from by simp [Lattice.affine], Poetry.rotates,← hf, pull_one]; rfl
  rw [Poetry.unearned n₀ H χ Ξ β γ B k htw V]; let v i:= Poetry.windup n₀ k H χ Ξ B β γ i V
  have he: ∑ i∈R₀,masked B.threshold ((Beam.marquee H B).reg i).support ((V₁).logRead i) V=∑ x:Site c,v x:= by
    unfold v Poetry.windup; rw [sum_comm]; symm; refine sum_congr rfl fun i hi=>?_ ; rw [← sum_mul,Meadow.paysOne,one_mul]; rfl
  rw [he]; unfold ornament; rw [Trio.parade]; simp_rw [sore,hp]; rw [sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul, card_univ]; unfold v; ring

omit hf htw
local notation "g₀" => (Poetry.sore n₀ k H χ Ξ B β γ z fa Q F₀ t₀)
-- t₀ ≤ ℓ. station.
lemma gained (hv:B.B=radiusB x)(hs:K₀≤ m)(i:Site c)(V:Config G c)(hU:Healthy B.threshold (neighbors m i) V): Poetry.windup n₀ k H χ Ξ B β γ i V=(P) i V:= by
  unfold Poetry.windup; rw [Poetry.aster n₀ H χ Ξ B β γ k, Finset.sum_apply]; refine sum_congr rfl fun j hj=> ?_
  by_cases hr : Meadow.garnerAt H B i j=0; · rw [hr]; simp
  have he:= (assigned n₀ H Ξ B i j hj hv hr).2
  exact congr_arg _ (masked_eq _ _ _ _ (hU.mono_left (fun p hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (he hi)).trans hs))))
include hB
lemma requiem (hw:w+4≤z) (hg: e>0)(hc:4*e+16 ≤ c.val)(he:2*e ≤ w)(hs: 2*z ≤ ℓ)(hp : K₀ ≤ e)(hF:t₀ ≤ ℓ)(i:Site c)(V:Config G c)(h : CompatibleP B e ((P)-F₀) fa)(hU:Healthy B.threshold (neighbors ℓ i) V): (g₀) i V=0:= by
  unfold sore; rw [Trio.cruising B Q z (rip fa) V i hw he hs hc hU _ (Trio.tinted _ _ h) hg,gained n₀ k H χ Ξ B β γ hB (show K₀ ≤ℓ from by omega) i V hU, masked_eq _ _ _ _ (hU.mono_left (show neighbors t₀ i⊆neighbors ℓ i from (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hF))))]; exact sub_self _

lemma tidy (hw:w+4 ≤z)(ht:K₀ ≤ ℓ)(hk: 2*z ≤ ℓ)(hF:t₀≤ℓ)(i:Site c) (hF':B.Regular (neighbors t₀ i) (F₀ i)) (hP : ∀ i j, B.Regular univ (fa i j))(hG:∀ i,B.Regular ((Beam.marquee H B).reg i).support ((gallery H χ β γ).logRead i)) : Tidy B (neighbors ℓ i) ((g₀) i):= by
  refine tidy_sub B (v:=Trio.unearned B Q z (rip fa) i) ?_ ?_
  · apply tidy_sub B _ (tidy_const B _); apply tidy_sub B _ (tidy_mask _ hF' (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hF)))
    refine tidy_sum _ _ R₀ _ fun j hj=> ?_; by_cases hB: Meadow.garnerAt H B i j=0; · simp only [hB,zero_mul]; exact tidy_const ..
    refine tidy_scale _ _ (tidy_mask _ (hG j) ?_)
    intro y hy; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((assigned n₀ H Ξ B i j hj (by assumption) (by assumption)).2 hy)).trans ht
  refine tidy_sum _ _ _ _ fun j _=> tidy_scale _ _ (tidy_sum _ _ _ _ fun i' _=> tidy_mask _ (unit_m B Q z fa hP hw (emerge Q j i' i) j i') (Trio.patch Q z hw j i' i hk))

include htw
lemma spray (V : Config G c)(i:Site c) : ‖Poetry.windup n₀ k H χ Ξ B β γ i V‖ ≤ (ballCost K₀:ℝ)*s:= by
  obtain ⟨a,ha,hX⟩:= htw.cheap
  let P':= Beam.marquee H B; let f i := ((Z').read V₁|>.regularOccurrence B i V)
  let R j:= Meadow.garnerAt H B i j
  unfold Poetry.windup; apply le_trans (norm_sum_le ..)
  let s':= neighbors K₀ i; let E i x:= if (P'.reg i).site=x then a i * Real.exp (preExponent B * coverNumber B.B (P'.reg i).support) else 0
  calc
    _ ≤ ∑ j∈ R₀, ∑ x∈s',E j x:= by
        apply sum_le_sum; intro j hj; have hp : 0≤∑ x∈s',E j x:=sum_nonneg fun x _=> (hX x).1 j
        change ‖R j*f j‖ ≤ _; by_cases ht:R j=0; · rw [ht,zero_mul,norm_zero]; exact hp
        have he:= (Poetry.assigned n₀ H Ξ B i j hj hB ht).2
        rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg (f j)) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (ha j) V).trans
        apply (le_mul_of_one_le_right (ha j|>.1) (Real.one_le_exp (show 0≤preExponent B * coverNumber B.B (P'.reg j).support from mul_nonneg (Song.headline B).exponent_pos.le (Nat.cast_nonneg _)))).trans
        unfold E; rw [sum_ite_eq,if_pos (he (P'.reg j).anchor)]
    _ ≤ (ballCost K₀:ℝ)*s:= by
        rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hX x) R₀))
        rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) htw.H_nonneg
lemma roofed (V:Config G c)(i:Site c)(hU: flags B.threshold V=∅): ‖(P) i V‖ ≤ (ballCost K₀:ℝ)*s:= by
  have ht:=gained n₀ k H χ Ξ B β γ hB le_rfl i V (show Healthy B.threshold (neighbors K₀ i) V from (by unfold Healthy; rw [hU]; simp))
  rw [← ht]; exact spray n₀ k H χ Ξ B β γ htw hB V i
lemma vint (V:Config G c) (i:Site c) (f : Stars→ℝ)(y:ℝ) (hq:∀ i (V:Config G (D i)), flags B.threshold V=∅→∀ x, ‖fa i x V‖ ≤ f i) (hp:w+4 ≤ z)(ha:B.supBounds i (neighbors t₀ i) (F₀ i) y) : ‖(g₀) i V‖ ≤ ((ballCost K₀:ℝ)*s+y) +((ballCost K₀:ℝ)*s+y) +∑ i:Stars,|Slide.ray i| * ((Fintype.card (Site (D i)):ℝ)*(f i+f i)) := by
  apply (norm_sub_le ..).trans; apply add_le_add ?_ (Trio.stipends B V Q z fa _ hq hp i)
  have hh:flags B.threshold (1:Config G c)=∅:= smoky («P»:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos)
  apply (norm_sub_le ..).trans ; refine add_le_add ((norm_sub_le ..).trans (add_le_add (spray n₀ k H χ Ξ B β γ htw hB V i) (CouplingShape.mask_cost ha V))) ((norm_sub_le ..).trans (add_le_add (roofed n₀ k H χ Ξ B β γ htw hB 1 i hh) ?_))
  exact ha.2 1 (by unfold Healthy; rw [hh]; simp) [] (Nat.zero_le _) (by simp)
end earnest
end YM.PhysicalNext.Repeat.Poetry
