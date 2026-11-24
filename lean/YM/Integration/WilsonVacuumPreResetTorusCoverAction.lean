import YM.Integration.WilsonVacuumPreResetTorusActionRead
import YM.Integration.FVA1Physical.TwoReset.Period

/-! The centered finite pre-reset action on all testing tori of the copied-period
limit. The copy normalization is taken at the fixed test side of MassCall. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusCoverAction
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
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments
open WilsonVacuumPreResetTorusActionRead (originalAction corrected)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (Covers coverFilter coverWin)
variable {G:Gauge}(R:Run G)

abbrev Cover (j:ℕ)(c:Side):=Covers R.family.S j c
def sheets (j:ℕ)(c:Side)(p:Cover R j c):ℕ:=((R.family.side j p.val).val/c.val)^4

def sample (N j i l:ℕ)(c:Side)(p:Cover R j c)(z:rule (Coarse G) c):ℂ:=
  (MvPolynomial.eval (Ker.convey (coverWin p.prop) z)
    (Blue.paint (l+1) (source R N j i (l+1) (R.family.side j p.val))):ℝ)

def record (N j i l:ℕ)(c:Side)(z:rule (Coarse G) c):ℂ:=
  (MvPolynomial.eval z (Blue.paint (l+1) (lagoon (output R N j i (l+1)) c)):ℝ)

theorem painted (simple:G.Simple){N j:ℕ}(older:j<N)(i l:ℕ)(c:Side)(z:rule (Coarse G) c):
    Tendsto (fun p=>(sheets R j c p:ℝ)⁻¹ • sample R N j i l c p z) (coverFilter R.family.S j c)
      (𝓝 (record R N j i l c z)):=by
  let n (p:Cover R j c):=R.family.side j p.val
  let M:=sheets R j c
  let W (p:Cover R j c):Macrame.Window c (n p) (M p):=coverWin p.prop
  let Z (p:Cover R j c):(Site (n p) × Hooks G) → ℝ:=WilsonVacuumPreResetTorusCopies.repeated (W p) z
  let cap:ℝ:=∑x:(Site c × Hooks G),‖z x‖
  have bounded (p:Cover R j c)(x:(Site (n p) × Hooks G)):‖Z p x‖≤cap:=
    Finset.single_le_sum (fun i _=>norm_nonneg (z i)) (Finset.mem_univ ((W p).cut x.1,x.2))
  have tracked:Yields (source R N j i (l+1)) (output R N j i (l+1)):=
    (perch R.family.path.levels R.metals.O simple (RunFormalChain.fromRun R).receipt older).growth i (l+1)
  obtain ⟨σ,A,warm,bill⟩:=tracked.cover
  have same:Yields (mismatch R N j i l) 0:=by
    simpa only [mismatch,sub_self] using tracked.sub (lagoon_yields bill warm tracked.road)
  have raw:=WilsonVacuumPreResetTorusIntensive.original _ same n ((grows R j).comp tendsto_comap) Z bounded
  have count (p:Cover R j c):Fintype.card (Site (n p))=M p*Fintype.card (Site c):=
    Shingle.received (W p).cut (W p).fold
  have positive (p:Cover R j c):(M p:ℝ)≠0:=by
    have nonzero:Fintype.card (Site (n p))≠0:=Fintype.card_ne_zero
    rw [count] at nonzero
    exact_mod_cast left_ne_zero_of_mul nonzero
  have scale (p:Cover R j c):(Fintype.card (Site c):ℝ)*(Fintype.card (Site (n p)):ℝ)⁻¹=(M p:ℝ)⁻¹:=by
    rw [count,Nat.cast_mul]
    field_simp
  have raw':Tendsto (fun p=>(M p:ℝ)⁻¹ •
      ((MvPolynomial.eval (Z p) (Blue.paint (l+1) (mismatch R N j i l (n p))):ℝ):ℂ))
      (coverFilter R.family.S j c) (𝓝 0):=by
    simpa only [FVA1Physical.TwoReset.coverFilter,smul_smul,scale,smul_zero] using raw.const_smul (Fintype.card (Site c):ℝ)
  have sums:=raw'.add (tendsto_const_nhds (x:=record R N j i l c z))
  rw [zero_add] at sums
  apply sums.congr' (Eventually.of_forall ?_)
  intro p
  have copy:=WilsonVacuumPreResetTorusCopies.painted (output R N j i (l+1)) bill warm (W p) z
  change (M p:ℝ)⁻¹ • ((MvPolynomial.eval (Z p) (Blue.paint (l+1) (mismatch R N j i l (n p))):ℝ):ℂ)+
      record R N j i l c z=(M p:ℝ)⁻¹ • sample R N j i l c p z
  change MvPolynomial.eval (Z p) (Blue.paint (l+1) (lagoon (output R N j i (l+1)) (n p)))=
    M p • MvPolynomial.eval z (Blue.paint (l+1) (lagoon (output R N j i (l+1)) c)) at copy
  simp only [mismatch,Pi.sub_apply,map_sub,Complex.ofReal_sub,smul_sub,copy,nsmul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_natCast]
  change (M p:ℝ)⁻¹ • sample R N j i l c p z -
    (M p:ℝ)⁻¹ • ((M p:ℝ) • record R N j i l c z) + record R N j i l c z = _
  rw [smul_smul,inv_mul_cancel₀ (positive p),one_smul,sub_add_cancel]



theorem original (simple:G.Simple){N j t:ℕ}(older:j<N)(Z:SeriesA G)(c:Side)
    (filed:∀l,corrected R N j Z c t (l+1)=lagoon (output R N j t (l+1)) c)
    (z w:rule (Coarse G) c):
    Tendsto (fun p:Cover R j c=>(sheets R j c p:ℝ)⁻¹ •
      ((evaluated (originalAction R N j (R.family.side j p.val)) t (convey (coverWin p.prop) z)-
        evaluated (originalAction R N j (R.family.side j p.val)) t (convey (coverWin p.prop) w):ℝ):ℂ))
      (coverFilter R.family.S j c)
      (𝓝 (((evaluated (corrected R N j Z c) t z-evaluated (corrected R N j Z c) t w):ℝ):ℂ)):=by
  let n (p:Cover R j c):=R.family.side j p.val
  let M:=sheets R j c
  let F:=corrected R N j Z c
  have bound:shellK 2 F:=mix_length (WilsonLimitConstruction.FundedSpringPeriodGerm.grade c
    (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) Z)
  have before (p:Cover R j c):((evaluated (originalAction R N j (n p)) t (convey (coverWin p.prop) z)-
      evaluated (originalAction R N j (n p)) t (convey (coverWin p.prop) w):ℝ):ℂ)=
      ∑l∈Finset.range (t+2),(sample R N j t l c p z-sample R N j t l c p w):=by
    have here:=WilsonVacuumPreResetTorusGrade.positive (originalAction R N j (n p))
      (WilsonVacuumPreResetTorusGrade.original R simple older (n p)) t
      (convey (coverWin p.prop) z) (convey (coverWin p.prop) w)
    simpa only [sample,WilsonVacuumPreResetTorusSeason.source,originalAction,n,
      Complex.ofReal_sum,Complex.ofReal_sub] using congrArg Complex.ofReal here
  have after:((evaluated F t z-evaluated F t w:ℝ):ℂ)=
      ∑l∈Finset.range (t+2),(record R N j t l c z-record R N j t l c w):=by
    have here:=WilsonVacuumPreResetTorusGrade.positive F bound t z w
    have sold (l:ℕ):F t (l+1)=lagoon (output R N j t (l+1)) c:=filed l
    simpa only [record,Complex.ofReal_sum,Complex.ofReal_sub,sold] using congrArg Complex.ofReal here
  have each (l:ℕ):Tendsto (fun p=>(M p:ℝ)⁻¹ •
      (sample R N j t l c p z-sample R N j t l c p w)) (coverFilter R.family.S j c)
      (𝓝 (record R N j t l c z-record R N j t l c w)):=by
    simpa only [smul_sub] using (painted R simple older t l c z).sub (painted R simple older t l c w)
  rw [after]
  change Tendsto (fun p=>(M p:ℝ)⁻¹ •
    ((evaluated (originalAction R N j (n p)) t (convey (coverWin p.prop) z)-
      evaluated (originalAction R N j (n p)) t (convey (coverWin p.prop) w):ℝ):ℂ)) _ _
  simp_rw [before,Finset.smul_sum]
  exact tendsto_finsetSum (Finset.range (t+2)) (fun l _=>each l)

end YM.Integration.WilsonVacuumPreResetTorusCoverAction
