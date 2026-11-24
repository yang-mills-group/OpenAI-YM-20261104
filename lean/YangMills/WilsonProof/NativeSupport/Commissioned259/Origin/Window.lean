import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Object

/-! # Application towards FIRST M.2 and the stronger powers of all the M.3 residuals

Work on one `Final` state and SAME t(r), exact H fields at both real scales. Everywhere
below the parameter `Z : ℝ → tower S` denotes those physical H (in particular from the position frame). Even if
that tower isn't the *chosen* J itself, the lemma applies. Take t the PositionHomogeneousFrame
reading. Include Viewer `none` (unselected) and arbitrary choices of phase & centre. Then,
conditioned on **only the additional analytic comparisons written in bbcb's proof**:

1. `Mileage.grows,fee`: growing version of G.1 for that exact field scale conversion (basis
   matrix entries, sup norm conventions of M.1). Use any one p' ≥ p+5 giving even g^(p+2) here.
   Keep the stated calibrated hypotheses on t as in M.1.
2. `Round` twice per query: G.9 on the SAME Hr (both Near & Far) physical reads on S, before
   doing the *different* Far conversion. One comparison on full profile K × E AND also on
   singleton centre `{0}` × **same** E. Need only evaluated basis cases.
3. `Seal`: (G.6) first inequality with this packet, these owner/viewer params (not moved
   between the two terms), exterior still at s! `seal_terms`. This is a physical estimate
   (relative to the reader `Q` on this same extraction). In addition to 1 and 2 for M.3. Buy
   that `δ` power ahead of `b`; H's inputs include those uniform size & split prices in
   the proof. Don't treat point limits as earning this comparison.

Use budgets for at least the indicated K,S and p,W's (Round from hScope thresholds).
For instance when buying the G prices in G's fixed geometries, `W ≥ 2` sufficiently large for
these compacts AND every hinted Flash259HorizonFork margin incl. if buying its G.6 with fixed
`δ,M`: clearance/enlargement and require `M ≤ δ * W` where so stipulated.
There is no assumption that the real exteriors lie on the temporary optical meshes here.

'Prepared' not another election or a vacuous supplier of the conclusion; unpack for those
known prerequisites of the M.1 analytic argument. We **consume**, not construct, those
prices in these implications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open OPE OPE.Orbits PhysMS FVA2.Scale Comparing O.Score O.Enh
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    {n m z h : ℕ} (d : Fin n→ℕ) (e : Fin m→ℕ) (hd : ∀ i, d i ≤ z) (he : ∀ i,e i ≤ z) (hh : h ≤ z)
    {U a b c W : ℝ} {K : Set (Points n)} {E : Set (Points m)}
    (hU : 0 ≤ U) (hK : IsCompact K) (hk : K⊆conf n) (hE : IsCompact E) (he' : E⊆Outside m)
    (hW : 1 ≤ W) (ha : clears W K E)
    {t : ℝ→ℝ} (paid : Calibrated G t) (p : ℕ)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion M ν

include H hK hk hU hW ha hE he' paid

/-- If paying the two analytic appointments in the NL proof, then the true Y & D with
H_s Far labels differ from the formal (after K and cropping) normalization, by the first-line
price of M.2. No payment here from that assumption on *these H_s-arm* differences. -/
theorem first (sched : Comparing.Prepared Vx Bx t (measures F Z d e)
    (measures F Z (fun (_:Fin 1)=>h) e) hd he hh (via Z) W a b K E p) :
    ∃ C : ℝ, 0 < C ∧ ∃ i : ℕ, ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a*(g0 G r)^(-b) →
      ∀ x∈K, ∀ y∈E, ∀ o, ∀ u∈Balls U G d, ∀ v∈ Balls U G e,
        ‖total F Z d e o r T x y u v-crop p (t r) (measurement Vx Bx hd he x (T • y) (-Real.log T) u v)‖ +
          opCost (centerD F Z h e o r T y v - predicted Vx Bx he hh (T • y) (-Real.log T) v p (t r)) ≤
            C*(T^(∑ j,e j)*(g0 G r)^(p+1))*(1+Real.log T)^i :=
  Comparing.M2_first hd he hh ((H.dilation ν).check) (H.separatedOPE ν).wilson hK hk hE he' hW ha hU sim paid _ _ p sched

/-- All prices of (M.3) INCLUDING the true packet insertion. `checkPrice` actually
uses D with the same Far scale, not a common upper bound. Power margin chosen by consumer.
Use `T` near the large endpoint `g(r)^(-b)`. -/
theorem M3 (hn : 0<n) (sched : Comparing.Prepared Vx Bx t (measures F Z d e) (measures F Z (fun (_:Fin 1)=>h) e)
      hd he hh (via Z) W a b K E p)
    (δ : ℕ) (budget : Seal (measures F Z d e) (measures F Z (fun (_:Fin 1)=>h) e)
       (coefficients F Z Q d h) (via Z) U a b W K E δ)
    (P : ℕ) (φ : ℝ) (hp : 0 < φ) (hc' : φ < 1)
    (hb : 0 < b) (hδ : (P:ℝ)+δ+1 ≤ b*(1-φ)) (hc : 0 < c) (hl : c ≤ a)
    (hup : P+b*((↑(∑ j,e j):ℝ)+h+φ)+1 ≤ p+1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, c*(g0 G r)^(-b) ≤ T → T ≤ a*(g0 G r)^(-b) →
      ∀ x∈K, ∀ y∈E, ∀ o, ∀ u∈Balls U G d, ∀ v∈ Balls U G e,
        checkPrice (total F Z d e o r T x y u v)
          (crop p (t r) (measurement Vx Bx hd he x (T • y) (-Real.log T) u v))
          (centerD F Z h e o r T y v) (predicted Vx Bx he hh (T • y) (-Real.log T) v p (t r))
          (coefficients F Z Q d h o r x u) (purchased Vx u x h p (t r)) ≤ C*T ^(-((h:ℝ)+φ))*(g0 G r)^P :=
  Comparing.M3_band hd he hh ((H.dilation ν).check) (H.separatedOPE ν).wilson hK hk hE he' hW ha hU sim paid _ _ p sched
    _ δ budget P hb hp hc' hup hδ hc

end YM.FVA2.GradedFar259.Original
