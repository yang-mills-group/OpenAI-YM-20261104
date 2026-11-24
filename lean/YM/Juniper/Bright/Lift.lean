import YM.Juniper.Bright.Pallet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps
/-!
# Wider halls & Post / superpayment.

 retag BEFORE Level Permit, keeping physical T.Book support. NO splitting
 low sources without Group. Fences are auxiliary only and keep every Group
 Kernel. pay Ribbon later.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {P: Side} {j i m n h N b:ℕ}

abbrev trek (b k:ℕ) := 20*(k+1)*(k+1)*(b+10)
abbrev mast (i:ℕ):=8*(i+2)
abbrev deep (i:ℕ):ℝ:= -((i:ℝ)+2)
theorem meaningful (i:ℕ) : -(3/8:ℝ)*(mast i) < deep i:= by unfold deep mast; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) i]

local notation "Y" => trek b n
local notation "r" => Mint.width b j j
local notation "u" => Meadow.studio Y j
local notation "v" => Trio.tent Y j
local notation "s" => Trio.fence Y j
local notation "z" => Trio.base Y j
lemma climb (hj:1≤j) : 0<u ∧ 2*j≤u ∧ Bright.Shelf.terrace r n ≤ u ∧ 2*u ≤ v ∧ v + 4 ≤ z ∧
     (∀ i:Stars,4*(u+r)+16 ≤ (s i).val ∧ 100*(1+j)≤ (s i).val) ∧ ∀ c:Side,2*z < c.val →4*(u+r)+16 ≤ c.val∧ 100*(1+j) ≤ c.val:=by
   have he: 2*j+1 ≤ u := by unfold Meadow.studio Meadow.roomSize; omega
   have hv : r+4 ≤ u:= by
      have hz:b ≤ Y:= ((show b≤b+10 from by omega).trans (le_mul_of_one_le_left (Nat.zero_le _) (by nlinarith only [Nat.zero_le n])))
      unfold Meadow.studio Meadow.roomSize Mint.width; have hp:= Nat.mul_le_mul_right j hz; omega -- needs b*j
   refine ⟨by omega, by omega,?_,(by unfold Trio.tent; omega), (by unfold Trio.base; omega), (fun i=>⟨?_, (Trio.highChair Y j i).2⟩),?_⟩
   · -- pay crossing n via ratio polynomial
     unfold Bright.Shelf.terrace Meadow.studio Meadow.roomSize Mint.width trek
     obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le hj -- orientation
     nlinarith only [Nat.zero_le (b*n*n*k), Nat.zero_le (b*n*n),Nat.zero_le (b*n),Nat.zero_le (b*n*k),Nat.zero_le b, Nat.zero_le (b*k), Nat.zero_le (n*k), Nat.zero_le (n*n*k), Nat.zero_le n, Nat.zero_le k]
   · change _≤ 2*(Trio.tent _ _ + _); unfold Trio.tent; omega
   intro c hc; unfold Trio.base Trio.tent at hc; omega
end YM.Juniper.Bright
