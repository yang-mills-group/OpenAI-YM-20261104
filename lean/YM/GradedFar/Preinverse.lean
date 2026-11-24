import YM.GradedFar.Travel
import YM.GradedFar.Packet
import YM.GradedFar.Combine
/-!
# NearFarDelta towards physical OPE, precise implementation of (M.3) under G1 G6 G9

Inserts the **actual tower twice** and keeps the full exterior. Shape arguments unchanged since
the formal price and same ν and p. In the application P is the H of the proof. Remains dependent
on actual physical running, Full/G6 and Pre/G9 hypotheses (made explicit in Ambient & downstream application).
These in particular include any-viewer (`Viewers F`) estimates. Not claiming the physical UV removal
is earned here.

We encode the precise cofinal quantifiers; given budgets on that exact instantiation for all B,
for any demanded p' = P_final and 0<η<1 take a sufficiently large B (>0, 'picks'); then p
sufficiently large. Use at ALL T between a and Λ times the moving scale in the statement.
Recursing further to inverse estimate also takes both measurements for its Far fields; no inference
about a disconnected estimate from these.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries Extraction Table Spec Climb PhysMS Trace.Pilot
open OPE (Viewers)
open OPE.Orbits (Reader)
open FVA2 XSpace XSpace.Normalize Register Scale Dframe O O.Score O.Enh FVA2.GradedFar
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (P : ℝ → tower S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (N : WilsonPrescription G) {hG : G.Simple} (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} (H : Main.Match N hG Z σ true) (ν : ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G
open FVA2.GradedFar.Budget

-- at price p paid over all T asymp within these windows. Include geometry r positive eventually automatically.
def BeforeInverse (t : ℝ → ℝ) (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m)) (a Λ η B : ℝ) (p' p : ℕ) : Prop :=
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ r in trail, ∀ T, receding (g r) B a Λ T → ∀ x ∈ K, ∀ y ∈ S',
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
        ∀ o (ω : Viewers F) (u : Inputs G d) (v : Inputs G e), Box u 1 → Box v 1 →
        let c := croppedVector A h p u x (t r)
        let Y := atLength F P ω o r T x y u v
        let dY := Y - crop p (t r) (fullSeries A W (-Real.log T) hd he x y u v)
        let D₀ := atCenter F P h ω o r T y v
        let dM := D₀ - croppedResponse A W (-Real.log T) hh he y v p (t r)
        ‖dY‖ + rowPrice dM + ‖dY-dM c‖ + ‖Y-D₀ (packet F P Q h o r x u)‖ + ‖Y-D₀ c‖ ≤
          L*(g r)^p'*T^(-(h:ℝ)-η)

variable {t : ℝ → ℝ} (ht : Coupling G t) {Λ B : ℝ} (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    {K : Set (Points n)} {S' : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
include H ht hK hx hS hy

theorem earned (p p' : ℕ) {a η D : ℝ} (ha : 0 < a) (hb : 0 < Λ) (hB : 0 < B) (hD : 0 ≤ D)
    (hz : p'+D+3 < B*(1-η)) (hp : p'+B*(FVA2.GradedFar.power e+h+η)+5 < p)
    (hW : ∀ i, FrameForecast P t W (e i) Λ B) (hf : RoundPoint F P t A hd he Λ B p K S')
    (hout : RoundPoint F P t A (d:=Output h) (fun _ => hh) he Λ B p {0} S')
    (purchased : PhysicalPacket F P Q d e h Λ B D K S') : BeforeInverse F P Q N Z ν t hd he hh K S' a Λ η B p' p := by
  obtain ⟨M,hM,k,T₀,hT₀,rM⟩ := first F P N Z H ν ht hK hx hS hy p hd he hh hW hf hout
  obtain ⟨A',hA,j,T₁,hT₁,rA⟩ := clocked N Z H ν ht hd he hh K S' hK hx hS hy p 1 zero_le_one
  obtain ⟨V,hV,T₂,hT₂,rV⟩ := purchased
  obtain ⟨S₁,h₁,Cp⟩ := vector_cap (d:=d) (H.separatedOPE ν).wilson hK hx h p 1 zero_le_one
  obtain ⟨L,hL,n₀,chooseG⟩ := combine (G:=G) ha hb hB hD hM hA.le hV p p' k j
    (FVA2.GradedFar.power e) hz hp h₁
  refine ⟨L,hL,?_⟩
  let hg := strength_falls hG
  have hup (T : ℝ) := hg.eventually (upwards hB ha T)
  filter_upwards [hg.eventually chooseG, rM, rA, rV,hup T₀,hup T₁,hup T₂,
    radius_falls hG n₀,clock_budget hG ht] with r hr hmt hat hvt h0 h1 h2 hx' hf
  intro T hT x hxx y hyy
  obtain ⟨hx₁,hx₂,Ht⟩ := hat T (h1 _ hT.1) x hxx y hyy
  refine ⟨hx₁,hx₂,?_⟩
  intro o ω u v hu hv
  exact hr _ hT _ hx' _ _ _ _ _ _ (Cp x hxx u hu _ hf.2.1)
    (hmt T (h0 _ hT.1) hT.2 x hxx y hyy o ω u v hu hv)
    (Ht u v hu hv) (hvt T (h2 _ hT.1) hT.2 x hxx y hyy o ω u v hu hv)

/-- This version spells out buying p *after* B, and can make it cofinally large.
T can vary anywhere in these windows (also can take `a=Λ=1` to use on that exact stretch). -/
theorem progresses {a η D : ℝ} (ha : 0 < a) (hb : 0 < Λ) (hη : η < 1) (hD : 0 ≤ D)
    (hW : ∀ B > 0, ∀ i, FrameForecast P t W (e i) Λ B)
    (hf : ∀ B > 0, ∀ p, RoundPoint F P t A hd he Λ B p K S')
    (hout : ∀ B > 0, ∀ p, RoundPoint F P t A (d:=Output h) (fun _ => hh) he Λ B p {0} S')
    (purchased : ∀ B > 0, PhysicalPacket F P Q d e h Λ B D K S') (p' : ℕ) :
    ∀ᶠ B in atTop, ∀ᶠ p in atTop, BeforeInverse F P Q N Z ν t hd he hh K S' a Λ η B p' p := by
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_gt_atTop ((p'+D+3)/(1-η))] with B hp' h0
  have hB := (div_lt_iff₀ (sub_pos.mpr hη)).mp h0
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (p'+B*(FVA2.GradedFar.power e+h+η)+5))] with p hp
  exact earned F P Q N Z H ν ht hd he hh hK hx hS hy p p' ha hb hp' hD hB hp
    (hW _ hp') (hf _ hp' _) (hout _ hp' _) (purchased _ hp')
end YM.Integration.GradedFar
