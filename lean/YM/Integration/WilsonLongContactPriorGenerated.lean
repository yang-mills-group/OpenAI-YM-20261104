import YM.RemainderComparison.Lyric.KForce

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorGenerated
open YM YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Daisy
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "λ₀" => mulScale ((tax G L x)⁻¹) l
local notation "F'" => Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)

open PhysicalNext.Repeat Mallow Merge.Photo Progress.DirectedRecipe
open Ovens
variable {R':Rep G f} (Y : Cash W x μ L Q o C T R') (D:Match.Alliance Y H 1 0) (V:BudgetPoint)
variable (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hx: V.threshold=Pressure.temp x)(he:V.B=radiusB x)
local notation "VB"=> Refrain.read Y D χ E t'
local notation "K₀"=> Palette.shoot M H χ λ₀ Y D

variable (visit:Bikes Q L μ x a L' B j n) (hl:YM.Merge.Palette.Plot M H (mulScale ((tax G L x)⁻¹) l))
include visit hl N hx he
theorem booked : Motion.Pays VB V K₀ F' a:=by
   constructor
   · intro j; unfold Palette.shoot; rw [show (ways λ₀ 0 j)=(fun _=>0) from (by ext; simp [Palette.ways]),Palette.at0 (t':=t') (E:=E)]
   · intro z w h; exact Palette.earned M H χ Y D V E t' hx (ways λ₀ z w)
   exact Palette.ready M H χ λ₀ hl visit N.balance Y D V E t' he


theorem original (roll:1≤grow G L x) :
    ∃ c:ℕ  → Finset ι→ℝ, (∀ i,∀ p,0 ≤ c i p ∧ ∀ U, ‖cod M H χ l Y D i U p‖ ≤ c i p) ∧
        Ac.Hit (fun i=>((VB).forced i).support) V.B (fun i=>∑ p:Finset ι, if p.card≤ k then c i p else 0) a ((tax G L x)^k*F'):=by
   have h := booked M H χ l N Y D V E t' hx he visit hl
   obtain ⟨g,hg,hK⟩:= h.bought
   choose b hb' hB hM using hg
   let C (i:ℕ)(p:Finset ι):=tax G L x^p.card*b i p
   have ht: 1≤ tax G L x:= one_le_pow₀ roll
   have hu: 0 < tax G L x:= zero_lt_one.trans_le ht
   have hz i p:0 ≤ C i p:=mul_nonneg (by positivity) (hb' i p)
   refine ⟨C,fun i p=> ⟨hz i p,fun U=>?_⟩,fun y=>?_⟩
   · obtain ⟨f,HX,h⟩:=hM i U; unfold cod; rw [HX.exact,norm_mul,Real.norm_of_nonneg (le_of_lt (pow_pos hu _))]; exact mul_le_mul_of_nonneg_left (h 0 ⟨le_rfl,zero_le_one⟩ p) (by positivity)
   -- x shadow; avoid
   have h := budget_scale (show 0 ≤ tax G L x^k from by positivity) (hK y)
   refine budget_loosen (budget_mono h ?_ ?_) (le_refl _)
   · intro i; dsimp only; split; next hh=> exact mul_nonneg (sum_nonneg fun i _=> by split; exact hz ..; exact le_rfl) (Real.exp_pos _).le
     next=>rfl
   intro i; dsimp only; split; next h=>
      rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right (le_trans ?_ (mul_le_mul_of_nonneg_left (hB _) (pow_nonneg hu.le _))) (Real.exp_pos _).le
      unfold Switch.high; rw [Finset.mul_sum]; refine sum_le_sum ?_; intro v _; split; next hp=> exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hp) (hb' ..)
      next=> exact mul_nonneg (by positivity) (hb' ..)
   rw [mul_zero]

end YM.Integration.WilsonLongContactPriorGenerated
