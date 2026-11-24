import YangMills.WilsonProof.NativeSupport.Commissioned259.Application.Physical
import YangMills.WilsonProof.NativeSupport.Commissioned259.Assay.All
/-!
# Continuing at the original M.2(different:first), M.3 demand

This is **on the continuum**; physical continuum, uniform viewer. Again all relative to the
noted previous §B…F purchases. Fix any sufficiently-large lower endpoint T0; purchase precision
then entirely on the same real branch. Compare full and center with the SAME converted Far
fields, layouts, weights; not testing an estimated matrix at other T. For more units, derivative or
inverse output assertions see `Price` and README.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalGradedFar
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.GradedFar259 FVA2.Scale FVA2.O.Score FVA2.O.Enh FVA2.O.Canon Dframe
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land GradedFar259.Application Pose
open YM.Integration.WilsonPositionPrescribedFrame
open YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
-- Original frame & horizon. Main.Match authentically; no relative choices. Even ν arbitrary.
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    (base : Leading F J) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "W" => WilsonPositionPrescribedFrame.positioned F J N.store
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "t" => WilsonPositionHomogeneousFrame.reading F J N

open Asymptotics GradedFar259.ScaleCost GradedFar259.Original GradedFar259.Comparing
local notation "Z" => WilsonPositionHomogeneousFrame.homogeneous F J N
local notation "A₀" => WilsonPositionHomogeneousNear.field N
local notation "ψ" => GroupS.ψ N.criterion M ν
variable (Y: Shop F (WilsonPositionPrescribedFrame.positioned F J N.store) N)
    (hp : ∀ d:ℕ, GradedFar259.Quotes.Mixture F (WilsonPositionPrescribedFrame.positioned F J N.store) N d)
local notation "g" => g0 G
variable (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hQ:LogTrace F Q.port)
    (Paid: GradedFar259.Flash.Pays F (WilsonPositionPrescribedFrame.positioned F J N.store) N)
include base H hQ hp Y ν Paid
variable {n m h z:ℕ} {d:Fin n→ℕ} {e:Fin m→ℕ} (hd:∀ i,d i≤z)(he:∀ i,e i≤z) (hh:h ≤ z)
  {L : ℝ} {K : Set (Points n)}{E : Set (Points m)} (hK:IsCompact K) (hc:K⊆conf n) (hS:IsCompact E)(hs:E⊆Outside m)(hL:0≤L)(P:ℕ) (η:ℝ) (hη:0<η) (hξ:η<1) (hn:0<n)
include hK hc hS hs
-- values for each basis, enough in M.2 first cost and in detector computation. Full proof
-- of (G.9) continuum estimate on these pin hypotheses in `Flash.Focus` (with its `afford`).
theorem G9book : ∀ᶠ T₀:ℝ in atTop,∀ a b:ℝ,0<a→0<b→ ∀ p:ℕ, Round V t (measures F Z d e) hd he p a b T₀ K E := by
  obtain ⟨D,X,hD,hX,A⟩:= GradedFar259.Flash.afford hK hc hS hs
  filter_upwards [Paid n m K E hK hc hS hs,A] with r v ⟨c,δ,l⟩ u b hu hb p
  exact GradedFar259.Flash.purchases F W Z N Q hQ (true_w F J N base) (true_normal F J N base) M H (real_frame F J N base M H (eligible F J N Y)) hp Y l hD hX v hu hb ν hd he p
include hL
lemma M2first : ∀ᶠ T₀:ℝ in atTop,∀ a b:ℝ,0<a→0<b→ ∀ p:ℕ,
    ∃ C:ℝ, 0<C ∧ ∃ i:ℕ, ∀ᶠ r in late, ∀ T ≥ T₀, T ≤ a*g r^(-b) →
      ∀ x∈K, ∀ y∈E, ∀ o, ∀ u∈Balls L G d, ∀ v∈Balls L G e,
        ‖Original.total F Z d e o r T x y u v - crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v)‖ +
          opCost (centerD F Z h e o r T y v - predicted V B he hh (T • y) (-Real.log T) v p (t r)) ≤
            C*(T^(∑ j,e j)*(g r)^(p+1))*(1+Real.log T)^i := by
   filter_upwards [eventually_ge_atTop (1:ℝ),always_clear hK hc hS hs, G9book F J N base ν M H Y hp Q hQ Paid hd he hK hc hS hs, G9book F J N base ν M H Y hp Q hQ Paid (fun (_:Fin 1)=>hh) he (isCompact_singleton (x:=(0:Points 1))) (singleton_subset_iff.mpr (injective_of_subsingleton _)) hS hs] with T hT hV hx hy a b ha hb p
   have paid0:= OriginalGradedFar.calibration F J N base M H (eligible F J N Y); exact Original.first F Z N ν M H d e hd he hh hL hK hc hS hs hT hV paid0 p ⟨ milestone Z H T hT hb (transition sim paid0) (G1 F J N base ν M H Y hp),hx a b ha hb p, hy a b ha hb p⟩
include hη hξ hn
lemma M3 : ∀ᶠ T₀:ℝ in atTop, ∀ᶠ b:ℝ in atTop,0<b ∧ ∀ᶠ p:ℕ in atTop, ∀ a c:ℝ,0<c→ c≤a →
    ∃ K':ℝ, 0<K' ∧ ∀ᶠ r in late, ∀ T ≥ T₀, c*(g r)^(-b) ≤ T → T ≤ a*(g r)^(-b) →
      ∀ x∈K, ∀ y∈E, ∀ o:Owner F, ∀ u∈Balls L G d, ∀ v∈Balls L G e,
        checkPrice (Original.total F Z d e o r T x y u v)
          (crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v))
          (centerD F Z h e o r T y v) (predicted V B he hh (T • y) (-Real.log T) v p (t r))
          (coefficients F Z Q d h o r x u) (purchased V u x h p (t r)) ≤ K'*T ^(-((h:ℝ)+η))*(g r)^P := by
  obtain ⟨C,hC,δ,hδ,A⟩:= arbitrarily_large hK hc hS hs
  filter_upwards [A,G9book F J N base ν M H Y hp Q hQ Paid hd he hK hc hS hs,G9book F J N base ν M H Y hp Q hQ Paid (fun (_:Fin 1)=>hh) he (isCompact_singleton (x:=(0:Points 1))) (singleton_subset_iff.mpr (injective_of_subsingleton _)) hS hs] with T₀ ⟨u,w,v⟩ hx hy
  filter_upwards [Original.listing F Z Q H (true_h F J N base M H (eligible F J N Y)) hQ hK hc hS hs u v hC hδ w hd he hh (G1 F J N base ν M H Y hp) hL (OriginalGradedFar.calibration F J N base M H (eligible F J N Y)) P η hη hξ hn] with b ⟨hb,hr⟩
  exact ⟨hb,hr.mono fun p h a c hc v=> h a c hc v (hx a b (hc.trans_le v) hb p) (hy a b (hc.trans_le v) hb p)⟩
-- prices and signed tests at real owner. measure variation. no moving y.
open GradedFar259.Assay
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
lemma M3test (ρ:ℂ→L[ℝ] F'→L[ℝ]ℂ)(hρ:‖ρ‖≤1) : ∀ᶠ T₀:ℝ in atTop, ∀ᶠ b:ℝ in atTop, ∀ᶠ p:ℕ in atTop, ∀ a c:ℝ,0<c→ c≤a →
    ∃ C :ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ T₀,c*g r^(-b) ≤ T → T ≤ a*g r^(-b) →
    ∀ X:Set E4, IsCompact X → ∀ u∈Balls L G d, ∀ v∈Balls L G e, ∀ q:Viewers F, ∀ μ:VectorMeasure (↥X × ↥K × ↥E) F', IsFiniteMeasure μ.variation →
        let o (i:↥X × ↥K × ↥E) := ((q,i.1.val) : Owner F); let x(i:↥X × ↥K × ↥E):=i.2.1.val; let y(i:↥X × ↥K × ↥E):=i.2.2.val
        Approval μ ρ (fun i=> Original.total F Z d e (o i) r T (x i) (y i) u v)
          (fun i=>crop p (t r) (measurement V B hd he (x i) (T • y i) (-Real.log T) u v))
          (fun i=> Original.centerD F Z h e (o i) r T (y i) v) (fun i=> predicted V B he hh (T • y i) (-Real.log T) v p (t r))
          (fun i=> Original.coefficients F Z Q d h (o i) r (x i) u) (fun i=> purchased V u (x i) h p (t r))
          (C*T^(-((h:ℝ)+η))*(g r)^P) := by
  obtain ⟨C,hC,δ,hδ,A⟩:= arbitrarily_large hK hc hS hs
  filter_upwards [A,G9book F J N base ν M H Y hp Q hQ Paid hd he hK hc hS hs,G9book F J N base ν M H Y hp Q hQ Paid (fun (_:Fin 1)=>hh) he (isCompact_singleton (x:=(0:Points 1))) (singleton_subset_iff.mpr (injective_of_subsingleton _)) hS hs] with T₀ ⟨u,w,v⟩ hx hy
  filter_upwards [eventually_gt_atTop (0:ℝ),Assay.filled F Z Q H (true_h F J N base M H (eligible F J N Y)) hQ hK hc hS hs u v hC hδ w ρ hρ hd he hh hL hn (OriginalGradedFar.calibration F J N base M H (eligible F J N Y)) (G1 F J N base ν M H Y hp) η hη hξ P] with b hb hr
  exact hr.mono fun p h a c hc v=> h a c hc v (hx a b (hc.trans_le v) hb p) (hy a b (hc.trans_le v) hb p)
end YM.Integration.OriginalGradedFar
