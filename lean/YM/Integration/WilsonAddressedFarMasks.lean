import YM.Integration.WilsonAddressedQuietPeer

/-! Keep both genuinely separated masks on their own original quiet owners
while testing the two actual occupied block products against the earlier
flat Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedFarMasks
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical

open WilsonAddressedQuietPeer WilsonThermometerEarlierWallet WilsonRootedKioskOccupiedSlip
open WilsonCapturedPrimarySoftPartition WilsonFullFaceSignedMasks Comparison.RG02.Cumulants
open Extra.Histories Next.Foundations Multi Push.AbsoluteSums Planned.GuardedAtom
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {N per m k b u : ℕ} (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin)
  (Ψ : ∀j, Rep G (R.family.side j per)) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (top : b ≤ N) {d : ℕ} {F : Frame G d} (S : SectionData F) (Y : Hol G)
  (simple : G.Simple) (way : WayStation R.kit)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (ticket : TicketP R.alloy R.kit D Q) (floor : m≤u) (ub : u≤b)
  (fixed : WilsonSingleHardRadius.first R simple≤u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "W" => Ψ b

include way ticket course top floor ub fixed S Y in
theorem original {V X ι : Type} [DecidableEq V] [Countable ι] {J : Census V}
    {o : V→Site (R.family.side b per)} (L : Lamps X ι G (W).p o J)
    (x : X) (s t : J.Mode) (q r : (parts J).Mode)
    (hq : q∈shards J s) (hr : r∈shards J t)
    (y z : Site (R.family.side b per)) (Z₁ Z₂ : Support (R.family.side b per))
    (h1 : y∈Z₁) (h2 : z∈Z₂) (a1 : ∀v∈s.val,o v∈Z₁) (a2 : ∀v∈t.val,o v∈Z₂)
    (r1 r2 : ℕ) (short1 : ∀v∈s.val,separation (o v) y≤r1)
    (short2 : ∀v∈t.val,separation (o v) z≤r2)
    (w : V→ℝ) (wp : ∀v,0<w v) {c d' : ℝ} (paid : L.Paid w (W).p.B ((W).p.supportExponent+2) c)
    (gross : Gross L w (W).p.B ((W).p.supportExponent+2) d')
    {σ E Λ δ v : ℝ} (K : Guard.Keeper (W).p (W).activities) (law : (W).Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth (W).p*v≤1)
    (p : ℕ) {ε : ℝ} (ep : 0<ε) (late : WilsonSingleHardRadius.start R simple p ep≤b) :
    let ρ := fun U => ((W).eval U:ℂ)
    let m₁ := covered L q x
    let m₂ := covered L r x
    let b₁ := declared L q x
    let b₂ := declared L r x
    let F₁ := fun U => ρ U*(m₁ U-b₁ U)*m₂ U
    let F₂ := fun U => ρ U*b₁ U*(m₂ U-b₂ U)
    let price₁ := wage w c r*(4*(1+|charge (W).p Z₁ w c d' v κ q|)*ε/β^p)
    let price₂ := wage w d' q*(4*(1+|charge (W).p Z₂ w c d' v κ r|)*ε/β^p)
    Admitted (u:=u) (N:=N) R (le_refl b) F₁ price₁ ∧
      Admitted (u:=u) (N:=N) R (le_refl b) F₂ price₂ ∧
      Admitted (u:=u) (N:=N) R (le_refl b) (fun U=>ρ U*(m₁ U*m₂ U-b₁ U*b₂ U)) (price₁+price₂) := by
  intro ρ m₁ m₂ b₁ b₂ F₁ F₂ price₁ price₂
  have width : 0 ≤ (W).p.supportExponent+2 := by linarith [(W).p.exponent_pos]
  obtain ⟨cm1,bm1,_,bp1⟩ := WilsonAddressedQuietPeer.filed L q x wp width paid gross
  obtain ⟨cm2,bm2,cp2,_⟩ := WilsonAddressedQuietPeer.filed L r x wp width paid gross
  obtain ⟨B₁,_,cap₁,owner₁⟩ := WilsonAddressedQuietAbsolute.partition (F:=F) L x s q hq y Z₁ h1 a1 r1 short1 w wp paid gross K law div hv room Y
  obtain ⟨B₂,_,cap₂,owner₂⟩ := WilsonAddressedQuietAbsolute.partition (F:=F) L x t r hr z Z₂ h2 a2 r2 short2 w wp paid gross K law div hv room Y
  have a : Admitted (u:=u) (N:=N) R (le_refl b) F₁ price₁ :=
    WilsonAddressedQuietPeer.one R π Γ Ψ course top S Y simple way D Q ticket floor ub fixed y
      (cm1.sub bm1) cm2 cp2 B₁ (fun U=>(cap₁ U).2.2) owner₁ p ep late
  have e : Admitted (u:=u) (N:=N) R (le_refl b) F₂ price₂ := by
    have earn := WilsonAddressedQuietPeer.one R π Γ Ψ course top S Y simple way D Q ticket floor ub fixed z
      (cm2.sub bm2) bm1 bp1 B₂ (fun U=>(cap₂ U).2.2) owner₂ p ep late
    have swapped : F₂ = fun U => ρ U*(m₂ U-b₂ U)*b₁ U := by funext U; dsimp only [F₂]; ring
    rw [swapped]
    exact earn
  have sum : (fun U=>ρ U*(m₁ U*m₂ U-b₁ U*b₂ U)) = F₁+F₂ := by
    funext U
    simp only [F₁,F₂,Pi.add_apply]
    ring
  rw [sum]
  refine ⟨a,e,a.1.add e.1,?_⟩
  intro j uj jb
  rw [WilsonThermometerUnitFilingRaw.add R F₁ F₂ a.1 e.1]
  exact (norm_add_le ..).trans (add_le_add (a.2 j uj jb) (e.2 j uj jb))

end YM.Integration.WilsonAddressedFarMasks
