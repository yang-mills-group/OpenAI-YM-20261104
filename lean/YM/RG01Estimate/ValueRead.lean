import YM.RG01Estimate.Cookie
/-!
# Jointly normed Taylor receipt, any supplied short-torus evaluation in the office class.
  This step compares to real-peano jets at the indicated lowering operation, with full
  Gaussian polynomial moments (untruncated domain). Must still supply IDENTIFICATION with
  powers of the independent Fk germ (including pivots & lower terms) prior to comparison.
  No projection of evaluated outputs to a weaker norm. Keep numerator integrals here relative
  to the lower-order base and cost scalar even with inserted analytic vacuum packets. Exact
  evaluation still all fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {L:Side}
section step
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio)(T:Tube G S) (ρ:Bid.Dir G c→ AxisChart G F)
    (k:S.Choices)(O: ChartRatio G)
local notation "X₀" => Positions (Uniform.Primary c G)
local notation "Y₀" => Poll.Body (Precision.Key F G)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
    (H:Poll.Body (Precision.Key F G)→ ℝ× Positions (Uniform.Primary c G) → E)
    (β D:ℝ)
local notation "d" => gStep β
local notation "M" => (Lapis.gram F T.up T.high ρ k)
local notation "μ₀" => Poll.sweep (M 0)⁻¹

def fill (z:Y₀)(y:ℝ × X₀):= voteForm (Lapis.table F k T.up T.high) (mist F O T.up) (Lapis.orbit F ρ) M z y • H z y

abbrev pullF (y:X₀) (z:Y₀) := H z (d, d⁻¹ • y)

local notation "U" => fill F T ρ k O H

lemma token (hp : 0<β) (x:X₀) : restricted F T O k ρ D (pullF F H β x) (d,x)=Office.held U (closedBall 0 D) (d,d⁻¹ • x) := by
  have ht : 0<d := (Fare.gS β hp).1
  funext i; unfold restricted Lantern.ballots Office.held
  by_cases h:i∈ closedBall 0 D
  · simp only [indicator_of_mem h]; unfold fill voteForm rho; dsimp only; rw [smul_inv_smul₀ ht.ne']
  simp only [indicator_of_notMem h,zero_smul]

lemma extent (hp : 0<β)(x:X₀) : Courtyard.weight F T O k ρ D (pullF F H β) β x= toric U (closedBall 0 D) μ₀ (d,d⁻¹ • x):= by unfold Courtyard.weight; rw [funext (congr_fun (token F T ρ k O H β D hp x))]; rfl

-- expensive unscaled directions used ONLY to price interpolation to seam at all real x.
variable [FiniteDimensional ℝ E] {C Y b:ℝ} {n:ℕ}
lemma charged (x:X₀) (he : 0<β) (hp : Roll U (closedBall 0 D) (ball (0:X₀) Y) b C n) (hc:0≤ C)
    (hx : (d,d⁻¹ • x)∈ corridor b (ball 0 Y)) :
      Brush n (C*(1+d⁻¹)^n) 1 (Courtyard.weight F T O k ρ D (pullF F H β) β) x := by
  let A := closedBall (0:Y₀) D; let f':=toric (fill F T ρ k O H) A μ₀
  let L':= d⁻¹ • ContinuousLinearMap.id ℝ X₀
  have hs : 0<d := (gS β he).1
  have hg : ‖L'‖ ≤ d⁻¹:= by rw [show L'=d⁻¹ • ContinuousLinearMap.id ℝ X₀ from rfl,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hs).le]; exact mul_le_of_le_one_right (inv_pos.mpr hs).le ContinuousLinearMap.norm_id_le
  have hF: Brush n C 1 f' (d,d⁻¹ • x):= Laplace.price_area _ _ _ _ hp isOpen_ball hc _ hx
  let L:= ContinuousLinearMap.inr ℝ ℝ X₀
  have hv x:(d,(0:X₀))+L x=(d,x):= by simp [L]
  have hm : Brush n C 1 (f' ∘ Lantern.arc d) (L' x):= by
    have h:= Lantern.skim (P:=L) (d⁻¹ • x) ((hv _) ▸ hF) n_hook
    simp only [hv] at h; exact h
  have h := Brush.reading L' hm hg; rw [one_mul] at h
  exact h.trim.shimmy (Eventually.of_forall (fun v=> extent F T ρ k O H β D he v))

def purses (N :ℕ)(y:X₀):= Laplace.chart (fill F T ρ k O H) Set.univ μ₀ N d y

def organic (g : Config G f→ E) := fun y:X₀=> Courtyard.invoice F T O k ρ β g (d • y)

-- local consumption. interior Taylor order n and derivative j. ħ supplies both.
lemma collects {g:Config G f→E} {R v W y fQ:ℝ} {N k':ℕ} (x:X₀) (hn : n+N ≤ k') {k₀} (he : 0 < β) (ph : d ≤ 1)
    (hQ : (M 0)⁻¹.PosDef) (hP : ∀ z, dotProduct z ((M 0)⁻¹*ᵥ z)≤ fQ*dotProduct z z)
    (hφ : (Fintype.card (Precision.Key F G):ℝ) ≤ W) (hv : 1≤ W)
    (hp : Roll (fill F T ρ k O H) (closedBall 0 D) (ball (0:X₀) Y) b C k') (hq : Atlas U (ball (0:X₀) Y) k₀ k' v) (hg:0≤ v) (hc:0 ≤ C)
    (hm : (d,x) ∈ corridor b (ball 0 Y))
    (hr : (∫ i in (closedBall (0:Y₀) D)ᶜ,(1+(‖i‖+1))^k₀ ∂μ₀) ≤ y)
    (hy : Brush n R 1 ((invoice F T O k ρ β g) - Courtyard.weight F T O k ρ D (pullF F H β) β) (d • x)):
       Brush n (R+(|d|^N*C+N*(v*y))) 1 ((organic F T ρ k O β g) -purses F T ρ k O H β N) x:= by
   have hh:= Laplace.chart_defect _ _ _ _ hq isOpen_ball hg fQ y W hp (show N ≤ k' by omega) (v:=d) (by rw [Real.norm_of_nonneg (Fare.gS β he).1.le]; exact ph) x hm measurableSet_closedBall hc hφ hv hQ hP hr
   let L:= d • ContinuousLinearMap.id ℝ X₀
   have hd:= (Fare.gS β he).1
   have hL: ‖L‖ ≤ 1:= by
      unfold L; rw [norm_smul,Real.norm_of_nonneg hd.le]
      exact (mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le).trans ph
   have he' := Brush.reading L (show Brush n _ _ _ (d • x) from hy) hL; rw [one_mul] at he'
   apply (he'.gathering (hh.smaller (show n ≤ k'-N by omega))).shimmy
   filter_upwards with z
   change invoice F T O k ρ β g (d • z)- chart _ _ _ _ _ _=(_-Courtyard.weight F T O k ρ D (pullF F H β) β (d • z))+(_-_)
   rw [extent F T ρ k O H β D he _,inv_smul_smul₀ hd.ne']; (rw [show L z=d • z from rfl]; abel)
end step
end YM.RG01Estimate.Laplace
