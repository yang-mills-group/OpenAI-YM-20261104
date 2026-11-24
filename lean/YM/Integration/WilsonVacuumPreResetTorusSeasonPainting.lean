import YM.Integration.WilsonVacuumPreResetTorusIntensive
import YM.Integration.WilsonVacuumPreResetTorusSeasonMoments
import YM.Integration.WilsonVacuumPreResetTorusCopies
import YM.Integration.WilsonVacuumPreResetTorusPhysicalPeriod

/-! The full independently submitted angular tensor on the original repeated
coarse test, normalized by its genuine number of copies. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusSeasonPainting
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments WilsonVacuumPreResetTorusPhysicalPeriod
variable {G:Gauge}(R:Run G)

def sample (N j i l per:ℕ)(z:rule (Coarse G) (base R.family.S j)):ℂ:=
  (MvPolynomial.eval (Ker.convey (window R.family.S j per) z)
    (Blue.paint (l+1) (source R N j i (l+1) (R.family.side j per))):ℝ)

def record (N j i l:ℕ)(z:rule (Coarse G) (base R.family.S j)):ℂ:=
  (MvPolynomial.eval z (Blue.paint (l+1) (lagoon (output R N j i (l+1)) (base R.family.S j))):ℝ)

theorem original (simple:G.Simple){N j:ℕ}(older:j<N)(i l:ℕ)
    (z:rule (Coarse G) (base R.family.S j)):
    Tendsto (fun p=>(copies R.family.S p:ℝ)⁻¹ • sample R N j i l p z) atTop
      (𝓝 (record R N j i l z)):=by
  let c:=base R.family.S j
  let n:=R.family.side j
  let M:=copies R.family.S
  let W (p:ℕ):Macrame.Window c (n p) (M p):=window R.family.S j p
  let Z (p:ℕ):(Site (n p) × Hooks G) → ℝ:=WilsonVacuumPreResetTorusCopies.repeated (W p) z
  let cap:ℝ:=∑x:(Site c × Hooks G),‖z x‖
  have bounded (p:ℕ)(x:(Site (n p) × Hooks G)):‖Z p x‖≤cap:=
    Finset.single_le_sum (fun i _=>norm_nonneg (z i)) (Finset.mem_univ ((W p).cut x.1,x.2))
  have tracked:Yields (source R N j i (l+1)) (output R N j i (l+1)):=
    (perch R.family.path.levels R.metals.O simple (RunFormalChain.fromRun R).receipt older).growth i (l+1)
  obtain ⟨σ,A,warm,bill⟩:=tracked.cover
  have same:Yields (mismatch R N j i l) 0:=by
    simpa only [mismatch,sub_self] using tracked.sub (lagoon_yields bill warm tracked.road)
  have raw:=WilsonVacuumPreResetTorusIntensive.original _ same n (grows R j) Z bounded
  have count (p:ℕ):Fintype.card (Site (n p))=M p*Fintype.card (Site c):=
    Shingle.received (W p).cut (W p).fold
  have positive (p:ℕ):(M p:ℝ)≠0:=by
    have nonzero:Fintype.card (Site (n p))≠0:=Fintype.card_ne_zero
    rw [count] at nonzero
    exact_mod_cast left_ne_zero_of_mul nonzero
  have scale (p:ℕ):(Fintype.card (Site c):ℝ)*(Fintype.card (Site (n p)):ℝ)⁻¹=(M p:ℝ)⁻¹:=by
    rw [count,Nat.cast_mul]
    field_simp
  have raw':Tendsto (fun p=>(M p:ℝ)⁻¹ •
      ((MvPolynomial.eval (Z p) (Blue.paint (l+1) (mismatch R N j i l (n p))):ℝ):ℂ))
      atTop (𝓝 0):=by
    simpa only [smul_smul,scale,smul_zero] using raw.const_smul (Fintype.card (Site c):ℝ)
  have sums:=raw'.add (tendsto_const_nhds (x:=record R N j i l z))
  rw [zero_add] at sums
  apply sums.congr' (Eventually.of_forall ?_)
  intro p
  have copy:=WilsonVacuumPreResetTorusCopies.painted (output R N j i (l+1)) bill warm (W p) z
  change (M p:ℝ)⁻¹ • ((MvPolynomial.eval (Z p) (Blue.paint (l+1) (mismatch R N j i l (n p))):ℝ):ℂ)+
      record R N j i l z=(M p:ℝ)⁻¹ • sample R N j i l p z
  change MvPolynomial.eval (Z p) (Blue.paint (l+1) (lagoon (output R N j i (l+1)) (n p)))=
    M p • MvPolynomial.eval z (Blue.paint (l+1) (lagoon (output R N j i (l+1)) c)) at copy
  simp only [mismatch,Pi.sub_apply,map_sub,Complex.ofReal_sub,smul_sub,copy,nsmul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_natCast]
  change (M p:ℝ)⁻¹ • sample R N j i l p z -
    (M p:ℝ)⁻¹ • ((M p:ℝ) • record R N j i l z) + record R N j i l z = _
  rw [smul_smul,inv_mul_cancel₀ (positive p),one_smul,sub_add_cancel]

end YM.Integration.WilsonVacuumPreResetTorusSeasonPainting
