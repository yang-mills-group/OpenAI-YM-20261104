import YM.GradedFar.Factor
/-!
# Lipschitz prices on admissible displacement from grid

Segments may differ by the r-charge file. Key property to charge is `Fits` at all points
of path including both ends, **holding T**. Physical placement at length r. Don't put in
G.9 estimate when changing the grid. Can use even just on v=none.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n m h:ℕ}
variable {K:Set (Points n)} {N:Set (Points m)} (hK:IsCompact K)(hx:K ⊆ conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)

namespace Crosser
local notation "avenueC"=> uIcc (0:ℝ) 1
local notation "Pt"=> Points (n+m)
abbrev segment (K:Set (Points n))(N:Set (Points m)) (p:Calendar) (q:Points (n+m)× Points (n+m)): Prop:=
    ∀ i ∈ (avenueC), Fits K N p.2 (slopePath q.1 (q.2 - q.1) i)

@[simp] lemma endsZero {n:ℕ}(x y: Points n): slopePath x y 0=x:= by simp [slopePath]
@[simp] lemma endsOne {n:ℕ}(x y: Points n): slopePath x (y-x) 1=y:= by simp [slopePath]
variable {U B:ℝ}
local notation "P∥" => moving G U B
include hK hx hN hz in
lemma safely : ∀ᶠ p in P∥,∀ q, segment K N p q → Walks q.1 (q.2-q.1) 0 1:=by
 filter_upwards [Dirty.upper hK hx hN hz] with p Hr q h i hi; obtain ⟨x,h₁,y,h₂,e⟩:= h i hi; rw [e]; exact Hr _ h₁ _ h₂
variable {t:ℝ→ℝ}{α:Future G h}(ht:Coupling G t)(hμ: Included F J h (h+1) (Nat.le_succ h))(hP:PaidFuture F J α t)
    (hX:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) h)
    (hY:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) (h+1))
variable {I:Type*}
private def lines (q : (Points (n+m) × Points (n+m)) × ↥avenueC): Points (n+m) := slopePath q.1.1 (q.1.2-q.1.1) q.2.val

lemma int_budget (f:ℝ→ℂ) {d:ℝ}(h:∀ x,x∈avenueC→‖f x‖≤d): ‖∫ x in (0:ℝ)..1,f x‖ ≤ d:= by
 refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun i hi=>h _ (uIoc_subset_uIcc hi))).trans_eq ?_; simp
include hK hx hN hz ht hμ hP
include H hX hY
lemma speculative (u:ListInput G (n+m) h)(k:ℕ): Sold P∥ (segment K N) (fun p _=>Δlog p)
    (fun _ q=> ‖q.2 - q.1‖) (fun _ q=> coeff k (sent X h q.2 u) - coeff k (sent X h q.1 u)):= by
 obtain ⟨j,c,hc,H'⟩:= Road.predicts Z M H hK hx hN hz (W:=fun p (q:(Pt × Pt)×↥avenueC) => segment K N p q.1)
    (z:=fun (p:Calendar) q=> lines q) (fun p q v=> v q.2.val q.2.property) α u k (fun p q=> q.1.2-q.1.1)
    (U:=U) (B:=B)
 refine ⟨j,c,hc,?_⟩; filter_upwards [H',safely hK hx hN hz] with p hr hs q hQ
 obtain H:= congrArg (coeff k) (fixedLine F J Z M H α ht hμ hX hY hP q.1 (q.2-q.1) (hs q hQ) u)
 rw [endsZero, endsOne,map_sub,operand,coeff_mk] at H; rw [H]; exact int_budget _ (fun i hi=> hr (q,⟨i,hi⟩) hQ)
lemma calculated (u:ListInput G (n+m) h)(k:ℕ): Sold P∥ (segment K N) (fun p _=>Δlog p)
    (fun _ q=> ‖q.2 - q.1‖) (fun p q=> crop k (t p.1) (sent X h q.2 u) - crop k (t p.1) (sent X h q.1 u)):= by
 simp_rw [← map_sub, crop_eq, map_sub (coeff _)]; let z:= Road.log_safety (U:=U) (B:=B) (G:=G) (W:=segment K N) (f:=fun p q=> ‖q.2-q.1‖)
    (Eventually.of_forall fun p q _=> norm_nonneg _); refine Fork.Sold.sum z (fun i _=>?_)
 obtain hp := speculative F J Z M H hK hx hN hz ht hμ hP hX hY u i (U:=U) (B:=B)
 obtain hB : Sold P∥ (segment K N) (fun p _=>Δlog p) (fun _ _=>1) (fun p _=> (t p.1:ℂ)^i):= by
    refine Fork.Sold.bounded (c:=1) zero_le_one ?_; filter_upwards [poses (clock_budget hG ht)] with p hh q hQ
    rw [norm_pow, mul_one, Complex.norm_real]; exact pow_le_one₀ (norm_nonneg _) hh.2.1
 simpa only [one_mul] using Fork.Sold.mul z hp hB
omit H hX hY
include hG
lemma earned (u:ListInput G (n+m) h) (v: Calendar→ (Pt × Pt)→Viewers F) (pay:G1Wide J Z M ν (h+1) t U B)
    (H:∃ D:ℝ,G6 F R J (Ceiling n (h+1)) (Ceiling m (h+1)) (h+1) U B D K N): Sold P∥ (segment K N)
    (fun p _=>wallet G p) (fun _ q=> ‖q.2-q.1‖) (fun p q=> frank F J (v p q) h p.1 q.2 u-frank F J (v p q) h p.1 q.1 u) := by
 obtain ⟨j,c,hc,H'⟩:= Road.payday F J R Z M ν hK hx hN hz (W:=fun p (q:(Pt × Pt)×↥avenueC) => segment K N p q.1)
    (z:=fun (p:Calendar) q=> lines q) (fun p q v=> v q.2.val q.2.property) hP pay ht H u (fun p q=> q.1.2-q.1.1)
    (fun p q=> v p q.1) (hG:=hG)
 refine ⟨j,c,hc,?_⟩; filter_upwards [H',safely hK hx hN hz,
    poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), poses (show ∀ᶠ r in trail,Going F J h r from hμ)] with p hr hs he hg q hQ
 obtain H:= earns F J (v p q) he hg q.1 (q.2-q.1) (hs q hQ) u; rw [endsZero, endsOne] at H; rw [H]; exact int_budget _ (fun i hi=> hr (q,⟨i,hi⟩) hQ)
end Crosser
end YM.Integration.GradedFar.Tariff
