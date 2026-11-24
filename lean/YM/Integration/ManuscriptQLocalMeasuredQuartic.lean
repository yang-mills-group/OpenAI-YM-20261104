import YM.Integration.ManuscriptQLocalGaussianQuartic
import YM.Integration.ManuscriptQLocalStoredGaussianScalar

/-! The signed scalar of the licensed measured aperture at order four,
including its retained physical cutoff remainder. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMeasuredQuartic
open Marker Bloch Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open Push.PriceCompiler PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonLimitConstruction FullQLocal.RenderedStep
open PhysicalAffineScalarFieldContraction PhysicalAffineScalarRootContraction ManuscriptQLocalGaussianQuartic
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "A₀" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

theorem divided {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ) {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : ((R.alloy.B.a.clock.op d.level d.period)).Choices) (q : Chi) (t : ℝ) (Y : LinkArray G (Frozen (noHole (R.alloy.B.a.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) d.forest)) (o : Site (R.alloy.B.a.clock.schedule.side d.level d.period))
    (h₄ : 4≤n (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)) (v : ι→((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ))) (a b c e : ι) :
    let s := ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o
    ContDiffAt ℝ 4 s 0 ∧ jet v s [a,b,c,e] 0 =
      jet v (ManuscriptQLocalGaussianScalar.scalar R d k d.forest o) [a,b,c,e] 0+
        (Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta)^4*jet v (ManuscriptQLocalScalarFields.regular R d k q t Y o) [a,b,c,e] 0 := by
  intro s
  let addJet := @FreeResolvent.TestD.jet_add ι ((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) ℝ Pi.normedAddCommGroup Pi.normedSpace Real.normedAddCommGroup _ v
  let f := ManuscriptQLocalScalarFields.regular R d k q t Y o
  let h := ManuscriptQLocalGaussianScalar.scalar R d k d.forest o
  have hf : ContDiffAt ℝ 4 f 0 := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p.2.1 k q t Y o) h₄
  have hh : ContDiffAt ℝ 4 h 0 := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.ideal_smooth R d p.1 k d.forest o) h₄
  have h₁ : ContDiffAt ℝ 4 f ((Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) • (0:((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)))) := by rw [smul_zero]; exact hf
  have hp : ContDiffAt ℝ 4 (fun B : ((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) => f ((Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) • B)) 0 := h₁.comp 0 ((Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) • ContinuousLinearMap.id ℝ ((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ))).contDiff.contDiffAt
  have he : s = fun B => h B+f ((Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) • B) := by
    funext B
    unfold s h f ManuscriptQLocalStoredGaussianScalar.stored ManuscriptQLocalGaussianScalar.scalar
      ManuscriptQLocalScalarFields.regular
    ring
  rw [he]; refine ⟨hh.add hp,?_⟩
  have pulled := @PhysicalAffineScalarIdealGrading.pulled_jet ι ((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) Pi.normedAddCommGroup Pi.normedSpace
    (Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) v f [a,b,c,e] hf
  exact (addJet [a,b,c,e] (A:=h) (B:=fun B : ((FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) => f ((Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) • B)) hh hp).trans
    (congrArg (fun r : ℝ => jet v h [a,b,c,e] 0 + r) pulled)

private theorem subtract_values {u f U F u₀ f₀ ρ z₁ z₀ z : ℝ}
    (hu : u=U+ρ*z₁) (hf : f=F+ρ*z₀) (h₀ : U-F=u₀-f₀) (hz : z=z₁-z₀) :
    u-f=(u₀-f₀)+ρ*z := by
  rw [hu,hf,←h₀,hz]
  ring

/-- The exact regular and one-forest measured fourth derivatives, with
the same original scalar remainder priced by the all-order cutoff bound. -/
theorem original {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀)
    (U : {V : Forest (S).ratio // changed S d.forest V z}) (Y : LinkArray G (Frozen A₀ θ d.forest))
    (Z : LinkArray G (Frozen A₀ θ U.val)) (o : Site c₀) (h₄ : 4≤n j₁ j₀) (v : ι→E) (a b c e : ι) :
    jet v (ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o) [a,b,c,e] 0 =
      completeCoefficient R d k d.forest o v a b c e+
        g₀^4*jet v (ManuscriptQLocalScalarFields.regular R d k q t Y o) [a,b,c,e] 0 ∧
    jet v (fun B => ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o B-
      ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o B) [a,b,c,e] 0 =
      (completeCoefficient R d k U.val o v a b c e-completeCoefficient R d k d.forest o v a b c e)+
        g₀^4*jet v (ManuscriptQLocalScalarFields.changedRoot R d k q t z U Y Z o) [a,b,c,e] 0 := by
  let subJet := @FreeResolvent.TestD.jet_sub ι E ℝ Pi.normedAddCommGroup Pi.normedSpace Real.normedAddCommGroup _ v
  let d' : LocalFormal.Datum R.family Γ := {d with forest:=U.val}
  obtain ⟨hf,eF⟩ := divided R d p k q t Y o h₄ v a b c e
  obtain ⟨hu,eU⟩ := divided R d' p k q t Z o h₄ v a b c e
  change ContDiffAt ℝ 4 (ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o) 0 at hu
  change jet v (ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o) [a,b,c,e] 0 =
    jet v (ManuscriptQLocalGaussianScalar.scalar R d k U.val o) [a,b,c,e] 0+
      g₀^4*jet v (ManuscriptQLocalScalarFields.regular R d' k q t Z o) [a,b,c,e] 0 at eU
  obtain ⟨eQ,dQ⟩ := ManuscriptQLocalGaussianQuartic.complete R d p.1 k d.forest U.val z o U.prop h₄ v a b c e
  refine ⟨eF.trans (congrArg (fun x : ℝ => x+g₀^4*jet v (ManuscriptQLocalScalarFields.regular R d k q t Y o) [a,b,c,e] 0) eQ),?_⟩
  have hU := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.ideal_smooth R d p.1 k U.val o) h₄
  have hF := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.ideal_smooth R d p.1 k d.forest o) h₄
  have eP := (subJet [a,b,c,e] (A:=ManuscriptQLocalGaussianScalar.scalar R d k U.val o)
    (B:=ManuscriptQLocalGaussianScalar.scalar R d k d.forest o) hU hF).symm.trans dQ
  have changed_eq : ManuscriptQLocalScalarFields.changedRoot R d k q t z U Y Z o =
      fun B => ManuscriptQLocalScalarFields.regular R d' k q t Z o B-
        ManuscriptQLocalScalarFields.regular R d k q t Y o B := by
    funext B; unfold ManuscriptQLocalScalarFields.regular ManuscriptQLocalScalarFields.changedRoot
    dsimp only [d']
    ring
  have hU' := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d' p.2.1 k q t Z o) h₄
  have hF' := smooth_of_le (ManuscriptQLocalStoredGaussianScalar.regular_smooth R d p.2.1 k q t Y o) h₄
  have changed_jet := (congrArg (fun f : E → ℝ => jet v f [a,b,c,e] 0) changed_eq).trans
    (subJet [a,b,c,e] (A:=ManuscriptQLocalScalarFields.regular R d' k q t Z o)
      (B:=ManuscriptQLocalScalarFields.regular R d k q t Y o) hU' hF')
  refine (subJet [a,b,c,e] (A:=ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o)
    (B:=ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o) hu hf).trans ?_
  exact subtract_values eU eF eP changed_jet

/-- All four input positions and the true varied tree site are summed
in the same complete bounds as the signed measured fourth derivative. -/
theorem price {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ) {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : ((R.alloy.B.a.clock.op d.level d.period)).Choices) (q : Chi) (t : ℝ) (U : ∀ z : Site (R.alloy.B.a.clock.schedule.side d.level d.period),{V : Forest ((R.alloy.B.a.clock.op d.level d.period)).ratio // changed (R.alloy.B.a.clock.op d.level d.period) d.forest V z})
    (Y : LinkArray G (Frozen (noHole (R.alloy.B.a.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) d.forest)) (Z : ∀ z, LinkArray G (Frozen (noHole (R.alloy.B.a.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) (U z).val))
    (o : Site (R.alloy.B.a.clock.schedule.side d.level d.period)) (h₄ : 4≤n (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)) :
    let N := n (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)
    let r := p.2.1.choose (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G ((Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level))) ((query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff ((query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) ((Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level))).L
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G ((Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level))) ((query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) N r*Real.exp (-(κ/2)*(till (R.alloy.B.a.clock.hatBeta d.level):ℝ))
    0<s ∧ 0<κ/2 ∧ (0<(Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta) ∧ (Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta)≤1) ∧
      Root 4 s o (fun _ : PUnit.{1} => o) (fun _ => ManuscriptQLocalScalarFields.regular R d k q t Y o)
        ((torusPay (PAC G 1) s)^4*ε) ∧
      Root 4 s o id (fun z => ManuscriptQLocalScalarFields.changedRoot R d k q t z (U z) Y (Z z) o)
        ((torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^4)*ε) := by
  intro N r s κ ε
  obtain ⟨hs,hκ,hw⟩ := ManuscriptQLocalScalarFields.original R d p.2
  exact ⟨hs,hκ,ManuscriptQLocalIdealSquare.fine R d p.1,hw k q t U Y Z o 4 h₄⟩

end YM.Integration.ManuscriptQLocalMeasuredQuartic
end
