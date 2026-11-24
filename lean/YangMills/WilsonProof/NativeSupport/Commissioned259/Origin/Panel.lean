import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Telescope
/-! # M.4 at the *genuine* physical detector (using the point choice of testing in the proof).
Chosen direction from centre to Far positive time, not negative (we use the example of
`FVA2/O/Read/Point`). Keep reflected-conjugate Far as the detector. The square matrix is
known at Maxwell leading, with uniform/compact phase pricing & Leading, not postulated.
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

variable {d : ℕ} {I : Type} {l:Filter I} {r T s : I → ℝ} (o : I→ E4) (p:I→Viewers F)
-- tables position. centerD for `Probe`; `S=physical`!
open FVA2.O.Read Matrix
lemma compress (p o r T b) :
    (instrument F Z d p o r T b).comp (via Z r (r*T) d) = Lens F Z d p o (r*T) b := by
  apply LinearMap.ext
  intro v; unfold instrument Lens; rw [LinearMap.comp_apply,centerD_apply,centerD_apply,mul_one,Original.shift]
  simp_rw [LinearEquiv.apply_symm_apply]
-- rank & primary p-high polynomial cost on inverse. Can already price this in upper range,
-- irrespective of further band.
variable {b a W:ℝ}
  (hr:Tendsto r l late)
  (θ : Calibrated G t) (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
  (hT : ∀ᶠ i in l,1≤ T i ∧ T i ≤ a*g0 G (r i)^(-b))
include θ S0 H hQ hZ hr hT
lemma rank (h:0<b) (d:ℕ) : (∀ᶠ i in l, IsUnit (Comparing.panel (instrument F Z d (p i) (o i) (r i) (T i)))) ∧
    (fun i=> stiffness (Comparing.panel (instrument F Z d (p i) (o i) (r i) (T i)))⁻¹) =O[l] (fun i=> T i ^ d) := by
  let D i:= instrument F Z d (p i) (o i) (r i) (T i); let E i:=(frame Z (r i*T i) d).trans (frame Z (r i) d).symm; let V i:=Lens F Z d (p i) (o i) (r i*T i)
  have h0 := hT.mono fun i h=>zero_lt_one.trans_le h.1
  have H' := cleared F Z Q H hZ (fun i=>S0.fields i 0) hQ o p (d:=d) (hull sim h0 hr (hT.mono fun i h=>h.2))
  have he : ∀ᶠ i in l,∀ u, (D i u).comp (E i).toLinearMap=V i u := Eventually.of_forall fun i u=>compress F Z (p i) (o i) (r i) (T i) u
  refine ⟨(Comparing.standard D V E H' he).mono fun i h=>h.1, matrixPay.mpr (Comparing.inverse D V E H' he ?_)⟩
  exact matrixPay.mp (issued_norms ((H.dilation ν).check) sim (transition sim θ) h (checks Z) S0 hr hT (reflexive Z)).1
end YM.FVA2.GradedFar259.Original
