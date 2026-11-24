import YM.Integration.WilsonPhysicalExteriorIssuedWord
import YM.Integration.WilsonPhysicalExteriorSmoothPrice

/-! Actual signed compact tests for every possible additional far
field in the physical degree horizon.  Each test operates on the
complete, independently dressed finite-minus-MS measured difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorTestedDetector
open Set Filter Function Real Finset MeasureTheory PowerSeries Lattice RG RG16
open PhysicalNext.Repeat.Legato Pert Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open FVA2 Register FVAAlt2 Lobby
open WilsonPhysicalExteriorIssuedWord
open scoped Topology BigOperators Classical
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {n:ℕ}
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)

structure Design (n:ℕ) where
  K:Set (Points (n+1))
  populated:Nonempty K
  out:Fin (n+1)→Bool
  detector:out (Fin.last n)=true
  A:ℝ
  δ:ℝ
  box_pos:0<A
  gap_pos:0<δ
  bounded:∀z∈K,∀i,‖Fountain.metric z i‖≤A
  radial:∀z∈K,∀i,out i=true → δ≤‖Fountain.metric z i‖
  apart:∀z∈K,∀i l,i≠l → out i=out l → δ≤‖Fountain.metric z i-Fountain.metric z l‖

def probe {h:ℕ} (p:Fin n→Label B) (a:Glyph B h) : Fin (n+1)→Label B:=
  Fin.lastCases (Lobby.owner a) p

theorem location {h:ℕ} (p:Fin n→Label B) (a:Glyph B h) :
    probe p a (Fin.last n)=Lobby.owner a ∧ ∀i:Fin n,probe p a i.castSucc=p i := by simp [probe]

def reader (R:Run G) (M:M₀) (Q:Prescription B₀) {h:ℕ} (p:Fin n→Label B₀) (D:Design n)
    (c c' μ:ℝ) (α eps:Fin (n+1)→ℝ) (u far:Fin (n+1)→Bool) (abs side:Bool) (k j per:ℕ)
    (f:Glyph B₀ h→Test (n+1)) (a:Glyph B₀ h) : ℂ :=
  (f a).applyTo (fun x=>difference R M Q (fun i=>(probe p a i).h) (fun i=>(probe p a i).item)
    c c' D.out (Fountain.metric x) μ α eps u far abs side k j per)

private theorem sample {m:ℕ} (f:Test m) (E:Points m→ℂ) (v ε:ℝ) (hv:0<v) (nonneg:0≤ε)
    (mass:(∫z,‖f z‖)≤1) (pt:∀z∈tsupport f,v*‖E z‖≤ε) :
    ‖f.applyTo E‖≤ε/v := by
  have hf:Integrable (fun z=>f z):=f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  calc
    _≤∫z,(ε/v)*‖f z‖:=by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
      apply Filter.Eventually.of_forall;intro z
      by_cases h:z∈tsupport f
      · rw [norm_mul,mul_comm (ε/v)]
        exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hv).mpr (by simpa [mul_comm] using pt z h)) (norm_nonneg _)
      · have hfz:f z=0:=by_contra fun he=>h (subset_closure he)
        simp [hfz]
    _=(ε/v)*∫z,‖f z‖:=integral_const_mul _ _
    _≤ε/v:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left mass (div_nonneg nonneg hv.le)

theorem measured (R:Run G) (M:M₀) (Q:Prescription B₀) (fund:Windows R M Q)
    (h:ℕ) (p:Fin n→Label B₀) (D:Design n) (c c':ℝ)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (RG16.Lambda R.family.path.levels m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ) (μ:ℝ) (α:Fin (n+1)→ℝ) (q:ℝ) (k t:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀u far:Fin (n+1)→Bool,∀abs side:Bool,
      ∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀eps:Fin (n+1)→ℝ,
      (∀i,exp (-WilsonPhysicalExteriorActualSides.time R c j)/WilsonPhysicalExteriorFirstCutScale.ratio R c' j≤eps i) →
      ∀f:Glyph B₀ h→Test (n+1),(∀a,tsupport (f a)⊆D.K)→(∀a,(∫z,‖f a z‖)≤1)→
      (WilsonPhysicalExteriorFirstCutScale.ratio R c' j)^t*
      ‖reader R M Q p D c c' μ α eps u far abs side k j per f‖≤exp (-q*RG16.Lambda R.family.path.levels j) := by
  letI:Nonempty D.K:=D.populated
  let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c'
  let Λ:=RG16.Lambda R.family.path.levels
  have buy(a:Glyph B₀ h):=fund (n+1) D.K (fun i=>(probe p a i).h) c c' D.out
    (fun z=>Fountain.metric z.val) slow h₁ h₂ h₃ lo D.A D.δ D.box_pos D.gap_pos
    (fun z=>D.bounded z z.property) (fun z=>D.radial z z.property) (fun z=>D.apart z z.property) μ α q k t
  filter_upwards [Filter.eventually_all.mpr buy] with j hj u far abs side per hp eps he f supp mass
  have ht:0<(T j)^t:=pow_pos (exp_pos _) t
  have hv:0≤exp (-q*Λ j)/(T j)^t:=div_nonneg (exp_pos _).le ht.le
  rw [mul_comm];apply (le_div_iff₀ ht).mp
  apply (pi_norm_le_iff_of_nonneg hv).mpr
  intro a
  apply sample (f a) _ _ _ ht (exp_pos _).le (mass a)
  intro z hz
  exact hj a (fun i=>(probe p a i).item) u far abs ⟨z,supp a hz⟩ side per hp eps he

end YM.Integration.WilsonPhysicalExteriorTestedDetector
end
