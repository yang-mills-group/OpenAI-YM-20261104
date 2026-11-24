import YM.Comparison.RG02.Assembly.Core
import YM.Comparison.RG02.Assembly.Contact
import YM.AnalyticNext.QUARTIC_MATCH.Scene
import YM.Work.F04.Choices
import YM.Extra.ITERATION_NO_LOSS.Calibration
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
/-!
# Full conditional Hessian at flat in Fk

Use `PathData`/Clip *themselves*, bind gauges & signs by deriving covariance from the real
 selected Wilson unmasked dotted basis. Holds in **counting** measure on physical periods; may
 also apply on an admitted virtual `StepData` with its own prices. Does not transport coefficients
 between these. Includes the conditional Markov Hessian penalty. Independent of physical predictor
 tag in the *germ*, not away from it. No constraints on curvature stencil end locations here
 except admissibility of those actual actions. No deformation of S or β beta-loop claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk
open Function Filter Finset MeasureTheory
open RG Precision Lattice Wilson Exterior Tree AnalyticNext.QuarticMatch
open Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f m : Side} (S : StepData c f) (p : Clip) (P : PathData G)
  (F : Forest S.ratio) (t : S.Choices) {k : ℕ} {a A Λ : ℝ}
-- annotate aliases less downstream duplication
abbrev Log := (fieldDir G c 1)
abbrev SliceDir (F : Forest S.ratio) (G : Gauge) := (Log (G:=G) (c:=c)) × AxisChart G F
abbrev Surface (z : SliceDir S F G) := uncurry (tested F t p P) z

lemma quadratic_pos (U : Config G m) : 0 ≤ quadratic p P U := sum_nonneg fun i _=>
  add_nonneg (mul_nonneg p.quadratic_pos.le (G.price_range _).1) (by positivity)
lemma quadratic_origin : quadratic p P (1:Config G m)=0 := by
  -- flat ell in cover coordinates
  have hp (i : Face (Per m)) : faceValue (1:Config G m) i=1 := by
     rw [← link_one]; exact Push.stroll_zero ..
  have hh (l : Slot) (x : Site m) : l.atSite (1:Config G m) x=0 := by rw [Work.F03.atSite_path,hp,G.curvature_unit,map_zero]
  simp [quadratic,hp,hh,PathData.ell,PathData.ellTerms]
lemma noise_pos (V : Config G c) (U : Config G f) : 0 ≤ noiseTaylor S V U t := mul_nonneg S.kernel.penalty_pos.le (sum_nonneg fun _ _=> (G.price_range _).1)
lemma noise_origin (hS : S.patch.Branches S.kernel G) : noiseTaylor S (1:Config G c) 1 t=0 := by
  have he : S.prediction (1:Config G f) t=1 := funext fun i=> Push.settled S hS i t
  simp [noiseTaylor,he]

open YM.Extra.Iteration
open YM.Extra.Iteration.Calibration (acted main core)
private lemma acted_empty {b : ℕ → Atom G k} (hs : 0 < a) (H : Charged b a A) (hk : 0<k) : acted b (0:fieldDir G m 1)=0 := by
  have he : iteratedFDeriv ℝ 0 (acted (n:=m) b) 0=0 := lower_jet hs H 0 hk
  exact (iteratedFDeriv_zero_apply ..).symm.trans (DFunLike.congr_fun he 0)
private lemma acted_first {b : ℕ → Atom G k} (hs : 0 < a) (H : Charged b a A) (hk : 1<k) : fderiv ℝ (acted (n:=m) b) 0=0 := by
  ext1 y; change fderiv ℝ _ _ _ = 0
  have he : iteratedFDeriv ℝ 1 (acted (n:=m) b) 0=0 := lower_jet hs H 1 hk
  exact (iteratedFDeriv_one_apply (fun _=> y)).symm.trans (DFunLike.congr_fun he _)

lemma core_origin : core (n:=m) P p 0 = 0 := by
  have h v : pull v 0 (1:Config G m)=1:=by funext i; unfold pull Step.read; split <;> simp
  simp [core,secondTerm,h, quadratic_origin,RG.Patch.average]

lemma core_first : fderiv ℝ (core (n:=m) P p) 0=0 := IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun b=> by
    change core _ _ _ ≤ _; rw [core_origin]; exact mul_nonneg (by positivity) (sum_nonneg fun i _=> quadratic_pos p P (pull i 0 (represent b))))

variable (hP : P.Bounds p a A Λ)
include hP in
lemma main_origin : main (n:=m) P p 0=0 := by
  rw [Calibration.splits]; exact (show _ from by
    simp only [Pi.add_apply,core_origin, acted_empty hP.width (show Charged _ _ _ from hP.three) (by decide : 0 < 3),
      acted_empty hP.width (show Charged _ _ _ from hP.four) (by decide : 0 < 4), zero_add])
include hP in
lemma main_first : fderiv ℝ (main (n:=m) P p) 0=0 := by
  have hc := (Calibration.core_jet (n:=m) hP).differentiableAt (by simp)
  have ht := (Calibration.acted_jet (n:=m) _ hP.width hP.three).differentiableAt (by simp)
  have hq := (Calibration.acted_jet (n:=m) _ hP.width hP.four).differentiableAt (by simp)
  rw [Calibration.splits, fderiv_add (hc.add ht) hq, fderiv_add hc ht, core_first,
    acted_first hP.width hP.three (by decide : 1<3), acted_first hP.width hP.four (by decide : 1<4), zero_add,zero_add]
include hP in
lemma loop_origin : loop P (1:Config G m)=0 := by rw [← link_one]; exact acted_empty hP.width hP.two (by decide)
include hP in
lemma loop_smooth : ContDiffAt ℝ ω (loop P (n:=m) ∘ represent) 0 := Calibration.acted_jet _ hP.width hP.two

local notation "fθ" => Surface S p P F t
local notation "E" => SliceDir S F G
local notation "M" => hessian F t p P 0 0
local notation "I" => Precision.Key F G
local notation "L" => Log (c:=c) (G:=G)

include hP
variable (hS : S.patch.Branches S.kernel G)
include hS
lemma origin : fθ 0=0 := by
  simp only [Surface,uncurry,tested,Prod.fst_zero, Prod.snd_zero, link_one,lifted,replica_one]
  -- undo
  have he : mainTerm p P (1:Config G f)=0 := by rw [← link_one]; exact main_origin p P hP
  rw [he,noise_origin S t hS,zero_add]
variable (b : fieldDir G c 1 → AxisChart G F) (hF : Critical F p P b)
include hF
lemma surface_first : fderiv ℝ fθ 0=0 := by
  let w (z : E) := mainTerm p P (Work.F03.live F z)
  let v := main P p ∘ Work.F03.axisLog (G:=G) F
  have he : v =ᶠ[𝓝 0] w := (Work.F03.inclusion_works F).mono fun z hz=> congrArg (mainTerm p P) hz
  let n (z : E) := noiseTaylor S (represent z.1) (Work.F03.live F z) t
  have hs : ContDiffAt ℝ ω fθ 0 := (hF.2.2 t).1
  have ht : ContDiffAt ℝ ω (Work.F03.axisLog (G:=G) F) 0 := (Work.F03.inclusion_smooth F).snd
  have hz : Work.F03.axisLog (G:=G) F 0=0 := congrArg Prod.snd (Work.F03.inclusion_zero F)
  have hm := show ContDiffAt ℝ ω (main P p) (Work.F03.axisLog (G:=G) F 0) from hz.symm ▸ Calibration.main_jet hP
  have hw : ContDiffAt ℝ ω w 0 := (hm.comp (f:=Work.F03.axisLog F) _ ht).congr_of_eventuallyEq he.symm
  have hw' : fθ=w+n := rfl
  have hn : ContDiffAt ℝ ω n 0 := by rw [show n=fθ-w by rw [hw']; abel]; exact hs.sub hw
  have hi : IsLocalMin n 0 := Eventually.of_forall fun y=> by
    have he' : n 0=0 := by unfold n; rw [Prod.fst_zero,link_one,Work.F03.live_zero]; exact noise_origin S t hS
    change n 0 ≤ n y
    rw [he']; exact noise_pos S t ..
  rw [hw', fderiv_add (hw.differentiableAt (by simp)) (hn.differentiableAt (by simp)), ← he.fderiv_eq, fderiv_comp (f:=Work.F03.axisLog F) _ (hm.differentiableAt (by simp)) (ht.differentiableAt (by simp)),hz,main_first p P hP, hi.fderiv_eq_zero, ContinuousLinearMap.zero_comp,zero_add]

open Matrix Work.F05
omit hP hF hS in
lemma hessian_tag (hS : S.patch.Branches S.kernel G) (r : S.Choices) : hessian F r p P 0 0=M := by
  have he : tested F r p P 0 =ᶠ[𝓝 0] tested F t p P 0 := ((tendsto_const_nhds (x:=(0:L))).prodMk_nhds tendsto_id).eventually
      (Work.F04.tested_germ hS ..)
  unfold hessian; rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds]

omit hP hS in
lemma surface_pos {η : ℝ} (Hη : 0<η) (H : PriceGap F p P η) : (M).PosDef := by
  -- `bend_det_pos` proof with positivity conclusion, retain basis
  rw [hessian_eq]; let C := countingBasis F G
  have hd : IsSymmSndFDerivAt ℝ (tested F t p P 0) 0 :=
    (((hF.2.2 t).1).comp (g:=fθ) (f:=fun y=>((0:L),y)) (0:AxisChart G F) (by fun_prop)).isSymmSndFDerivAt_of_omega
  apply PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact (show _ from by simp only [transpose_apply, LinearMap.toMatrix₂_apply]; exact hd (C j) (C i))
  intro x hx
  rw [star_trivial]; have he : x ⬝ᵥ (LinearMap.toMatrix₂ C C (bend (tested F t p P 0) 0) *ᵥ x) = _ := dotProduct_toMatrix₂_mulVec C C (bend (tested F t p P 0) 0) x x
  rw [he]; exact tested_diag Hη H t _ (fun hh=> hx (C.equivFun.symm.injective (hh.trans (map_zero _).symm)))

-- curvature: translate by *linear* stationary slope before reading order coefficients.
def classical (x : fieldDir G c 1) := tangent b 0 x
omit hP hS hF in
@[simp] lemma classical_point (x : fieldDir G c 1) : classical S F b x=(x,fderiv ℝ b 0 x):=rfl

def shiftedDir (x : fieldDir G c 1) (v : AxisChart G F) := classical S F b x + (0,v)
def infrared (x : fieldDir G c 1) := Assembly.jet (Surface S p P F t) 2 (classical S F b x)

omit hS hP in
/-- Complete square identity with coarse term on linear stationary slope. -/
lemma flat_square (x : fieldDir G c 1) (v : AxisChart G F) :
    Assembly.jet fθ 2 (shiftedDir S F b x v) = infrared S p P F t b x + bend (tested F t p P 0) 0 v v/2 := by
   let w := classical S F b x
   have hp (z : E) : Assembly.jet fθ 2 z = bend fθ 0 z z / 2 := by
     have hh : (fun _:Fin 2=>z)=![z,z] := by funext i; fin_cases i <;> rfl
     simp_rw [Assembly.jet, hh, ← bend_apply]; norm_num [Nat.factorial]; ring
   have he : OnShell fθ b 0 := SliceExchange.on_shell t hF
   have h1 : bend fθ 0 w (0,v)=0 := by
      have hf:= he.flat x v; rw [show arc b 0=0 from Prod.ext rfl hF.1] at hf; exact hf
   have h2 : IsSymmSndFDerivAt ℝ fθ 0 := (hF.2.2 t).1.isSymmSndFDerivAt_of_omega
   have h3 : bend fθ 0 (0,v) w=0 := (h2 (0,v) _).trans h1
   have h4 : bend fθ 0 (0,v) (0,v)=bend (tested F t p P 0) 0 v v := by
      let L' := ContinuousLinearMap.inr ℝ L (AxisChart G F)
      have hg : tested F t p P 0=fθ ∘ L' := rfl
      -- linear precomposition
      rw [hg,bend_apply,bend_apply]
      have hf : ContDiffAt ℝ (↑(2:ℕ)) fθ (L' 0) := L'.map_zero.symm ▸ (hF.2.2 t).1.of_le le_top
      rw [Assembly.contact_right L' hf,L'.map_zero]
      change _= (iteratedFDeriv _ _ _ _) (fun i=> L' (![v,v] i)); congr 1; funext i; fin_cases i <;> rfl
   unfold shiftedDir infrared
   rw [hp,hp]; change bend fθ 0 (w+_) (w+_)/2=_
   simp_rw [LinearMap.map_add, LinearMap.add_apply]; rw [h1,h3,h4]; change _= bend fθ 0 w w /2+_; ring

omit hP hF hS in
lemma tape_price (x : I→ℝ) : tape (G:=G) (ι:=F.Free) x=(countingBasis F G).equivFun.symm x := by
   let H := countingBasis F G
   rw [Module.Basis.equivFun_symm_apply]
   have he : ∀ i:I, H i=gaugeCount (ι:=F.Free) (Pi.single i 1) := fun i=> (countingBasis_apply ..).trans (on_axis (G:=G) i).symm
   change gaugeCount x = ∑ i,x i • H i
   simp_rw [he,← map_smul gaugeCount, ← map_sum]; congr 1; ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]

omit hP hF hS in
lemma hessian_force  (H : (M).PosDef) (x : I→ℝ) : bend (tested F t p P 0) 0 (tape x) (tape x)=Gaussian.force M⁻¹ x := by
   rw [tape_price S F]
   unfold Gaussian.force; rw [Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ H.det_pos.ne'),hessian_eq]; exact (dotProduct_toMatrix₂_mulVec _ _ (bend (tested F t p P 0) 0) x x).symm

end YM.Comparison.RG02.Bulk
