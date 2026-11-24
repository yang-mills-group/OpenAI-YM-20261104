import YM.Integration.WilsonNeutralPointAppointment

/-! The original physical-election interface for the individual child operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointForecast
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open FormalBulk08 FormalBulk08.Flat WilsonLimitConstruction.FundedCompanySelection
open WilsonNeutralPointAppointment

variable {G:Gauge}

def Enrolled (K:KernelChoices)(A:Levels G):Prop:=
  let F:=(Labels.frames G).level
  let H:=hol G
  let W:=Borough.windowBasis G K
  (∀ j,∀ c:Request G j,before K F H W c≤((A.clock.factor j).val:ℝ)) ∧
  ∀ i,∀ c:Request G (A.clock.J (i+1)),∀ P:Patch,∀ S:Lodge P,
    P.L=A.S.block i → P.J=A.clock.J (i+1) →
    |after K F H W c P S|≤ Borough.ageZ (A.clock.hatBeta i)

def Filed :Prediction G:=fun {M} {_} {A} _=>Enrolled M.p.kernel A.B.a

theorem prepaid (s:Sheet G)(price:MapPrices):WilsonFundedWindowMenu.Prepared (@Filed G) s price:=by
  intro C E flags programs wages baton
  let K:=s.kernel
  let F:=(Labels.frames G).level
  let H:=hol G
  let W:=Borough.windowBasis G K
  refine ⟨floor K F H W,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  let q (j:ℕ)(x:ℝ):Prop:=∀ c:Request G j,∀ R:Patch,∀ S:Lodge R,
    R.L=D.L j → R.J=j → |after K F H W c R S|≤Borough.ageZ x
  obtain ⟨raised,other,_,pay⟩:=delay_extra V q (fun _ _ _=>True) (fun j=>by
    obtain ⟨B,_,price⟩:=buy_after K F H W (D.L j) j
    filter_upwards [Borough.age_fly.eventually (eventually_ge_atTop B)] with x high
    exact fun c M S hL hJ=>(price c M S hL hJ).trans high)
    (fun _ _=>Filter.Eventually.of_forall fun _=>trivial)
  refine ⟨raised,other,?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q₀ exchange aux rider booth sheltered works divides
  constructor
  · intro j c
    have grow:floor K F H W j≤(B.a.clock.factor j).val:=by
      rw [B.valid.lengths]
      exact (hl j).trans (D.large j).need
    exact (floor_pays K F H W c).trans (by exact_mod_cast grow)
  · intro i c M S hL hJ
    have side:M.L=D.L (B.a.clock.J (i+1)):=by
      rw [hL,←B.a.fits.sameFactor i,B.valid.lengths]
    exact (pay Y hY).1 _ _ (B.valid.pays i) c M S side hJ

theorem original (R:Run G)(roll:Filed R.kit)(i:ℕ)(c:Request G (R.family.path.levels.clock.J (i+1)))
    (S:Lodge ((R.family.path.levels.clock.op i 0).patch))
    (live:ready R.metals.p.kernel (Borough.windowBasis G R.metals.p.kernel) c):
    let K:=R.metals.p.kernel
    let F:=(Labels.frames G).level
    let W:=Borough.windowBasis G K
    ∃ b:ℝ,b≤Borough.ageZ (R.family.path.levels.clock.hatBeta i) ∧
      fits K F W c (R.family.path.levels.clock.op i 0).patch S b:=by
  intro K F W
  obtain ⟨h,cost⟩:=roll
  let P:=(R.family.path.levels.clock.op i 0).patch
  let b:=after K F (hol G) W c P S
  have gate:before K F (hol G) W c≤(P.L.val:ℝ):=by
    have z:=h _ c
    change before K F (hol G) W c≤((R.alloy.B.a.clock.factor (R.alloy.B.a.clock.J (i+1))).val:ℝ) at z
    rw [R.alloy.B.a.fits.sameFactor i] at z
    exact z
  refine ⟨b,(le_abs_self _).trans (cost i c P S rfl rfl),?_⟩
  exact paid K F (hol G) W c live P gate S

end YM.Integration.WilsonNeutralPointForecast
end
