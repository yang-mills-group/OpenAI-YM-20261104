import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Family
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Calendar
/-! # Further to `Window`: earn M.3 directly (given RoundMeter etc. of BB proof)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {n m z h:ℕ} {L M δ W a b c:ℝ} {d:Fin n→ℕ} {e:Fin m→ℕ}
    {A:Set (Points n)}{B:Set (Points m)}
    (hA:IsCompact A)(h'A:A⊆conf n) (hB:IsCompact B)(h'B:B⊆Outside m)
    (hW:1≤W)(hw:clears W A B) (hM:0≤M)(hδ:0<δ)(hF:Clears W M δ A B)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion O ν
local notation "g"=> g0 G

include H hq hZ hQ hW hM hδ hF h'B
-- for O(h) estimates a and b requested *after* exponent on fields.
lemma town : ∃ z : ℕ, ∀ a b:ℝ,
    Seal (measures F Z d e) (measures F Z (fun (_:Fin 1)=>h) e) (coefficients F Z Q d h) (via Z) L a b W A B z := by
  obtain ⟨C,hC,k,A'⟩:= G6 F Z Q H hZ hq hQ (d:=d) (e:=e) (L:=L) hM hδ h
  refine ⟨k,fun a b=>⟨C,hC.le,?_⟩⟩
  let X:={i:ℝ×ℝ // i.2 ≥ W ∧ i.2 ≤ a*g i.1^(-b)}; let r (i:X):= i.val.1; let T (i:X):= i.val.2
  let V:=Filter.comap r late
  have y : Tendsto (fun i:X=> r i*T i) V late := hull sim (Eventually.of_forall fun i=>zero_lt_one.trans_le (hW.trans i.property.1)) tendsto_comap (Eventually.of_forall fun i=> i.property.2)
  have P:= eventually_comap.mp (y.eventually A')
  filter_upwards [P,self_mem_nhdsWithin] with r P hr T hT ht x hx y hy o u hu v hv
  have he:(trueD F Z r (r*T) o.2 o.1 y.ofLp v h)=probed (measures F Z (fun (_:Fin 1)=>h) e) (via Z) o r T y v := (center_upon F Z e o hr (zero_lt_one.trans_le (hW.trans hT)) (h'B hy) v).symm
  change ‖total F Z d e _ _ _ _ _ _ _ - probed _ _ _ _ _ _ _ (trueC F Z Q r o.2 x.ofLp u h)‖ ≤ _; rw [total_eq, ← he]; have p:= (P (⟨(r,T),hT,ht⟩:X) rfl _ _ _ (hF _ hx _ hy _ hT r hr) o.2 o.1 o.1 u hu v hv).1
  refine p.trans_eq ?_ ; change C*(g r)⁻¹^k*(r*T+(r/(r*T))^(h+1))= _; rw [show r/(r*T)=T⁻¹ by change 0 < r at hr; field_simp]

variable (hd:∀ i, d i≤z) (he:∀ i,e i≤z) (hh:h≤z)
omit hq
variable (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
   (h₁:0≤L) (hm:Calibrated G t)
local notation "Qy" => (measures F Z d e)
local notation "Qz" => (measures F Z (fun (_:Fin 1)=>h) e)

include hA h'A hB hw hm h₁ S0
/-- Actual M.3 band, **assuming** the G.9 reading comparison & G.1 on compact ratios
and earlier calibration and LogTrace pins. Exponent on G.6 not an input anymore. Use either
prepared earlier interfaces or this version to pay on the actual hierarchy (not cutoff estimates).
Use `BB` parameter choice also for inverse queries e.g. use these eventual filters and
finite sets of those tasks. -/
theorem listing (P:ℕ) (η:ℝ) (hp:0<η) (hc:η<1) (hn:0<n): ∀ᶠ b:ℝ in atTop,
    0<b ∧ ∀ᶠ p:ℕ in atTop, ∀ a c:ℝ, 0<c→ c≤a →
      Round Vx t Qy hd he p a b W A B →
      Round Vx t Qz (fun _=>hh) he p a b W {0} B →
        ∃ K:ℝ, 0<K ∧ ∀ᶠ r in late, ∀ T ≥ W, c*(g0 G r)^(-b) ≤ T → T ≤ a*(g0 G r)^(-b) →
        ∀ x∈A, ∀ y∈B, ∀ o, ∀ u∈Balls L G d, ∀ v∈Balls L G e,
          checkPrice (total F Z d e o r T x y u v)
            (crop p (t r) (measurement Vx Bx hd he x (T • y) (-Real.log T) u v))
            (centerD F Z h e o r T y v) (predicted Vx Bx he hh (T • y) (-Real.log T) v p (t r))
            (coefficients F Z Q d h o r x u) (purchased Vx u x h p (t r)) ≤ K*T ^(-((h:ℝ)+η))*(g0 G r)^P := by
  obtain ⟨z,Z'⟩:= town F Z Q H hZ (fun i=> S0.fields i 0) hQ (d:=d) (e:=e) (L:=L) (h:=h) h'B hW hM hδ hF
  filter_upwards [chooseBudget (∑ i,e i) h z P hc] with b ⟨hb,hz,H'⟩
  refine ⟨hb,H'.mono fun p q a c hv hv' u v=>?_⟩; exact Original.M3 F Z Q N ν O H d e hd he hh h₁ hA h'A hB h'B hW hw hm p hn
    ⟨ milestone Z H W hW hb (transition sim hm) S0, u,v ⟩ z (Z' a b) P η hp hc hb hz hv hv' q
end YM.FVA2.GradedFar259.Original
