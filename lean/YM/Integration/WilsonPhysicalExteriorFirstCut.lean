import YM.Integration.WilsonPhysicalExteriorActualSides
import YM.Integration.WilsonPhysicalExteriorNativeLog
import YM.Integration.WilsonPhysicalExteriorPeriodPair
import YM.Integration.WilsonEpochPostedComparison
import YM.Integration.WilsonPositionProgramPrescription

/-! The original independently renormalized finite Wilson MS rows at the
first physical ultraviolet stop, for every deposited real period and the
prescribed auxiliary period. The subtraction log is allowed to vary after
the regulator because its finite polynomial degree is uniform. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFirstCut
open Function Filter Set Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone MS.Logarithm
open FVA2 Register YM.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorResolvedReadout
open WilsonPhysicalExteriorResolvedCutoff WilsonPhysicalExteriorUVStory
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G)
local notation "Λ₀" => RG16.Lambda R.family.path.levels
variable {n:ℕ} {B:MS.Local.Physical.Deck G} {H:Booked B} (M:MS_Data G H)
variable (Q:Prescription B) (D:Fin n→Label B) (c:ℝ) (W:Fin n→ℕ→ Cover)

def scene (actualSide:Bool) (u:ℝ) : Trial Point (Fin n) :=
  if actualSide then field R c u W
  else WilsonPhysicalExteriorPrescribedSide.change (field R c u W) (fun z=>Λ₀ z.1)

def signed (actualSide:Bool) (k:ℕ) (u:ℝ) (z:Point) : ℂ :=
  Lobby.evaluateR R.metals.O (basisR R) Q D (scene R c W actualSide 0) u k z -
    tour M D u (testP (field R c 0 W) z) Finset.univ k

variable (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
variable (hc:1≤c)(hc₂:c<2) (lo:ℕ→ℕ)
variable (reach:Reach (WilsonPhysicalExteriorActualSides.geometry R c 0) (field R c 0 W).off)
variable (apart:Resolved (WilsonPhysicalExteriorActualSides.geometry R c 0) (info (field R c 0 W).off))
variable (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)

private theorem common_row (side:Bool) (u:ℝ) (k:ℕ) (z:Point) :
    Lobby.evaluateR R.metals.O (basisR R) Q D (scene R c W side u) u k z -
        tour M D u (testP (scene R c W side u) z) Finset.univ k =
      signed R M Q D c W side k u z := by
  cases side <;> rfl

private theorem common_clock (side:Bool) (u:ℝ) (z:Point) :
    (scene R c W side u).profile.θ z = WilsonPhysicalExteriorActualSides.time R c z.1 := by
  cases side <;> rfl

include reach apart in
private theorem same_geometry (u:ℝ) :
    Reach (WilsonPhysicalExteriorActualSides.geometry R c u) (field R c u W).off ∧
      Resolved (WilsonPhysicalExteriorActualSides.geometry R c u) (info (field R c u W).off) :=
  ⟨reach,apart⟩

private theorem genuine (u:ℝ) : scene R c W true u=field R c u W := rfl
private theorem auxiliary (u:ℝ) : scene R c W false u=
    WilsonPhysicalExteriorPrescribedSide.change (field R c u W) (fun z=>Λ₀ z.1) := rfl

private theorem both_domains (hG:G.Simple)
    (hs:∀m:ℕ,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (hl:1≤c) (hu:c<2) (lower:ℕ→ℕ)
    (rr:Reach (WilsonPhysicalExteriorActualSides.geometry R c 0) (field R c 0 W).off)
    (aa:Resolved (WilsonPhysicalExteriorActualSides.geometry R c 0) (info (field R c 0 W).off))
    (u:ℝ) :
    Domain (field R c u W) (channel R c lower) u ∧
    Domain (WilsonPhysicalExteriorPrescribedSide.change (field R c u W) (fun z:Point=>RG16.Lambda R.family.path.levels z.1)) (channel R c lower) u :=
  @WilsonPhysicalExteriorActualSides.rooms G R n hG hs c hl hu lower u W
    (@same_geometry G R n c W rr aa u).1 (@same_geometry G R n c W rr aa u).2

private theorem certified (hG:G.Simple) (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (hc:1≤c) (hc₂:c<2) (lo:ℕ→ℕ)
    (reach:Reach (WilsonPhysicalExteriorActualSides.geometry R c 0) (field R c 0 W).off)
    (apart:Resolved (WilsonPhysicalExteriorActualSides.geometry R c 0) (info (field R c 0 W).off))
    (actualSide:Bool) (u:ℝ) :
    Domain (scene R c W actualSide u) (channel R c lo) u := by
  cases actualSide
  · rw [auxiliary]
    exact (both_domains R c W hG slow hc hc₂ lo reach apart u).2
  · rw [genuine]
    exact (both_domains R c W hG slow hc hc₂ lo reach apart u).1

include hG paid in
private theorem sampled (actualSide:Bool) (k:ℕ) (u:ℝ)
    (table:Domain (scene R c W actualSide u) (channel R c lo) u) :
    ∃ A:ℝ,0<A ∧ ∀ᶠ z : Point in channel R c lo,
      ‖signed R M Q D c W actualSide k u z‖≤A*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c z.1) := by
  have comp := WilsonPhysicalExteriorResolvedReadout.measured
    (T:=scene R c W actualSide u) (l:=channel R c lo) (μ:=u)
    R.metals.O (basisR R) Q D M R.alloy.B.ratio table hG paid k
  obtain ⟨A,hA,good⟩ := comp.2
  refine ⟨A,hA,?_⟩
  filter_upwards [good] with z hz
  rw [← common_row R M Q D c W actualSide u k z,← common_clock R c W actualSide u z]
  exact hz

include apart in
private theorem degrees (actualSide:Bool) (k:ℕ) :
    Ready (signed R M Q D c W actualSide k) := by
  have finite:=WilsonPhysicalExteriorNativeLog.finite R.metals.O (basisR R) Q D (scene R c W actualSide 0) k
  have inject : ∀ z,Function.Injective (testP (field R c 0 W) z) :=
    fun z=>WilsonPhysicalExteriorResolvedReadout.geometry (presented (μ:=0) _ apart) z
  exact finite.sub (MSExteriorFiniteScales.tour_polynomial M D (testP (field R c 0 W)) inject k)

theorem corrected (hG:G.Simple) (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (hc:1≤c) (hc₂:c<2) (lo:ℕ→ℕ)
    (reach:Reach (WilsonPhysicalExteriorActualSides.geometry R c 0) (field R c 0 W).off)
    (apart:Resolved (WilsonPhysicalExteriorActualSides.geometry R c 0) (info (field R c 0 W).off))
    (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q) (actualSide:Bool) (k:ℕ) :
    ∃ A:ℝ,0≤A ∧ ∃ d:ℕ,∀ᶠ j:ℕ in atTop,∀ per≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀ u:ℝ,
      ‖signed R M Q D c W actualSide k u (j,per)‖≤
      A*(1+|u|)^d*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j) := by
  obtain ⟨N,A,hA,d,inter⟩:=MSExteriorFiniteScales.finite_observations (degrees R M Q D c W apart actualSide k)
  choose K hK price using fun i:Fin N=>sampled R M Q D c W hG lo paid actualSide k (i.val:ℝ)
    (certified R c W hG slow hc hc₂ lo reach apart actualSide i.val)
  let fee:ℝ:=1+∑ i:Fin N,K i
  have hf:0≤fee:=add_nonneg zero_le_one (Finset.sum_nonneg (fun i _=>(hK i).le))
  refine ⟨A*fee,mul_nonneg hA hf,d,all_later R (c:=c) (lo:=lo)
    (P:=fun z:Point=>∀ u:ℝ,‖signed R M Q D c W actualSide k u z‖≤
      A*fee*(1+|u|)^d*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c z.1)) ?_⟩
  filter_upwards [Filter.eventually_all.mpr price] with z hz u
  have nodes (i:ℕ) (hi:i∈Finset.range N) :
      ‖signed R M Q D c W actualSide k (i:ℝ) z‖≤fee*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c z.1) := by
    let t:Fin N:=⟨i,Finset.mem_range.mp hi⟩
    have under:K t≤∑ i:Fin N,K i:=Finset.single_le_sum (fun a _=>(hK a).le) (Finset.mem_univ t)
    exact (hz t).trans (mul_le_mul_of_nonneg_right (show K t≤fee by dsimp [fee];linarith)
      (exp_pos _).le)
  apply (inter z u _ (mul_nonneg hf (exp_pos _).le) nodes).trans_eq
  ring

end YM.Integration.WilsonPhysicalExteriorFirstCut
end
