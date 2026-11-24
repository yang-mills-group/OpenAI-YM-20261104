import YM.LocalTaylorR2.Strange.Pod
import YM.LocalTaylorR2.Reel.Furl
/-! # Auxiliary tower books ON THAT Spring. Not from unaligned vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Strange
open Exponent
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- include useful grade-specific setup using transported PTO Argument exponents.
open CalendarStep
local notation "❖" => Chi.canonical
section slate
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
variable (b:BudgetPoint) (X:Match.Alliance I H 1 0) (v:ℝ) (p:ℕ)(Ξ:Observatory G) (φ:Bool) (n:ℕ)
abbrev stellar:= cohort H («χ»:=❖) X v (M:=p) (Mesh.issue H (Ξ.upgrade H p) ❖) φ (fun i=>if φ then ¬ p+1 ≤ i else p+1 ≤ i)
end slate
open Rain Roost Mallow Capstone
variable {G:Gauge} {M:Metals G} {D:Rolls M.p} {A:Alloy M D} (Ξ:Observatory G) (R:Factor A) {hm' : G.Simple} {l k: ℝ} {m n N:ℕ} {Q:In A.B.a m n} (H:Spring R N m n l k Q) (x:ℝ) (hx:x∈Icc l k) (p:ℕ) (φ:Bool) (hp:Mallow.RG12.Earned (Exponent.reckon Ξ) R.shape A.delay)
local notation "y"=> A.B.a.clock.hatBeta m
local notation "y₁"=> A.B.a.clock.hatBeta (m+1)
local notation "z"=> Trio.base (Rain.lint R.target A m) (radiusB y)
local notation "k₀"=> Rain.lint R.target A m
local notation "j₁"=> A.B.a.clock.J (m+1)
local notation "j₀"=> A.B.a.clock.J m
local notation "Z"=> A.B.a.S.side m n
local notation "B" => A.B.a.budget m
local notation "v"=> A.B.kin.alpha N m
local notation "P"=> (H.H.latch x)
local notation "d"=> H.ordinal
local notation "U"=> H.H
local notation "u"=> Rain.noteX H.H H.knows x
local notation "T"=> H.W
set_option quotPrecheck false
local notation "Omo"=> (Rain.moor R.target A m)
local notation "J"=> Rain.screens R.target A m
local notation "Φ"=> H.V'
local notation "κ"=> (Φ) x
def plume (i:Stars) :=
    let Y:=H.W.tiers i (u)
    stepsAt Y B (stellar Y (show Match.Alliance Y Y 1 0 from Match.staple rfl rfl rfl) v p Ξ φ) d
abbrev perpetual : ∀ i:Stars,Trio.Offer G (Omo i):= plume Ξ R H x p φ
abbrev pillar := Trio.ornament (J) (perpetual Ξ R H x p φ) (c:=Z)
variable (hY : p ≤ A.B.a.clock.J (m+1)) (hm:m<N)
local notation "a"=> Capstone.fare k₀ (A.B.a.params m) y
local notation "s"=> CalendarStep.loss j₁
local notation "o"=> (y₁^(requested (p+1) s))
include hp hY hm
local notation "Z₀"=> (perpetual Ξ R H x p false)
local notation "P₀"=> (Rain.beacons H.H H.knows H.W (d) x)
local notation "Ω"=> (fun i:Stars=>2*(Fintype.card (Site (Omo i)):ℝ)*o)
lemma allstars : H.W.offers (d) (u)=perpetual Ξ R H x p true+perpetual Ξ R H x p false ∧ ∀ i:Stars,(∀ j,(B).Regular univ (Z₀ i j)) ∧ ∀ (W:Config G (Omo i)), flags (B).threshold W=∅ → ∀ l:List (Directions G (Omo i)), l.length≤(B).order → (∀ h∈l,‖h‖≤(B).threshold) → ‖leftDerivs (Boulevard.stillA (Trio.froth (Z₀ i))) l W‖ ≤ Ω i:=by
  let Y (i:Stars) := H.W.tiers i (u)
  let v' (i:Stars): Match.Alliance (Y i) (Y i) 1 0:=Match.staple rfl rfl rfl
  let A' (i:Stars):= stellar (Y i) (v' i) v p Ξ
  have h (i:Stars) : ((T).offers (d) (u) i)=perpetual Ξ R H x p true i+perpetual Ξ R H x p false i ∧ Meadow.Budget B (Beam.marquee (Y i) B).reg (A' i false|>.logRead) o:=by
    obtain ⟨C,e,f,g,y₀,l₁,l',r,B',q,v₀,k',a₁,θ,j,N',he⟩:= loaded Ξ R (Rain.panes R.target A m i) (H.W.tiers i (u)) hm hp p hY (s) le_rfl
    constructor
    · rw [show (T).offers (d) (u) i=Meadow.barony (Y i) ❖ (d) (v) from rfl, terms_bloom (Y i) B (v' i) rfl rfl rfl]
      exact terms_chain (Y i) B d (by simpa only [stellar,Bool.false_eq_true,ite_false,ite_true] using! YM.LocalTaylorR2.subtract (Y i) he.probed (v' i) (v) (fun i'=> p+1 ≤ i'))
    have hz:= bequeath Ξ R (Rain.panes R.target A m i) (Y i) he (v' i) (le_refl (p+1)) (fun i'=> p+1 ≤ i') (fun _ hi=>hi)
    simpa only [A',stellar,Bool.false_eq_true,ite_false] using! hz
  exact ⟨funext (fun i=> (h i).1), fun i=> ⟨watch (Y i) B (A' i false) (h i).2 d,fun j h' l h₁ h₂=> rails (Y i) B (A' i false) (h i).2 d j h' l h₁ h₂⟩⟩

lemma pinnacles : let U':=pillar Ξ R H x p false; let f:=oroW B z Ω
    P₀=pillar Ξ R H x p true+U' ∧ Meadow.Budget B (Marlin.leap z) U' (f*Real.exp (preExponent B*coverTicket k₀)) := by
  intro X' f
  obtain ⟨hf,hp⟩:= allstars Ξ R H x p hp hY hm
  have he:0≤o:=Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _
  have hK (i:Site Z):= Capstone.pace B J z Z₀ (fun j=> (hp j).1) (q:=Ω) (fun i=> by positivity) (by unfold Trio.base; omega) i (fun j=> (hp j).2)
  have hv : 0≤f:= (hK 0).2.1
  refine ⟨funext (fun (i:Site Z)=> Capstone.offers_add J ((T).offers (d) (u)) i _ _ hf),fun i=>f,fun i=>?_,fun i=> hK i⟩ -- tuple
  apply budget_finite
  · intro i; split; exact mul_nonneg hv (Real.exp_pos _).le; rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (leap z i).site=i from rfl)]
  · apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters k₀ (radiusB y) (B).B_pos i z (by omega)).trans; rw [two_mul]
  · intro j hj he; exact if_neg he
  simp
end YM.LocalTaylorR2.Strange
