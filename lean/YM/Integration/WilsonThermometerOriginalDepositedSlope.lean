import YM.Integration.WilsonThermometerOriginalClockSlope
import YM.Integration.WilsonThermometerRegisteredAngularJet

/-! Smoothness of every deposited student face in the held field at the measured adjacent reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalDepositedSlope
open FVA1Physical.TwoReset
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Cumulants.Cloud
open Extra.Trajectories Primitives.GCC.Anchor QuadraticLocal Earn
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}

omit [Fintype V] in
theorem copied {ι α:Type} {f:Side} {J:Passport n V} (multiple:n.val∣f.val)
    (M:ι→Row J R G α) (w:V→ℕ) (L:AllOrder.Floe.Layout G) (T:Finset AllOrder.Floe.Age)
    (v:α) (d:ℕ) (s:R.Mode) : Differentiable ℝ (fun a:Stationary.Link G f=>
      (peek multiple M w L T v d a).part s) := by
  exact ((WilsonThermometerRegisteredAngularJet.coefficient 1 _ d s).differentiable (by norm_num)).comp
    (Stationary.arm G f 1).differentiable


open AllOrder AllOrder.Floe AllOrder.Floe.Step PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal.Rebirth QuadraticLocal.Advent.Oak Comparison.RG02 Comparison.RG02.Adjacent

/-- The same dated lesson fixes both the zero and linear parts of the additive kinetic correction. -/
theorem income (run:Run G) {m i k N:ℕ}
    (hk:Burn.horizon k+2 ≤ run.alloy.B.a.clock.J m)
    (D:PlanV.Roots (G:=G) run.metals.p.profile run.metals.K run.metals.p.kernel) (Q:D.Tab run.rolls)
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hi:m ≤ i) (L:Lesson (N:=N) run hk D Q π Γ hi) :
    ∃a,Pace.Earn (Γ i) a := by
  rw [L.eats]
  exact ⟨_,(PlanV.litP D run.alloy Q (hk.trans (run.alloy.B.a.fits.mono hi)) L.entry).sustenance.due L.entry⟩

omit [Fintype V] in
/-- The complete upper coefficient is copied on all held fields before it is fed back into the
next block. The scalar inverse clock contributes no first variation on this same copy. -/
theorem table {ι α:Type} {f:Side} {J:Passport n V} (multiple:n.val∣f.val)
    (M:ι→Row J R G α) (w:V→ℕ) (L:Layout G) (T:Finset Age) (v:α)
    (p depth:ℕ) (live:0<p) (q:Pace.Coin) (a:ℝ) (earned:Pace.Earn q a)
    (value : ℕ → Stationary.Link G f→Poly R)
    (full:∀d≤p,∀x,value d x=peek multiple M w L T v d x) (s:Multi.Hot R) (x:fieldDir G f 1) :
    let K:=(caliber q earned.1).back depth
    WilsonOriginalCoverJetColors.reset p value K s 0 x=(value 0 ((Stationary.arm G f 1).symm x)).part s.val ∧
      WilsonOriginalCoverJetColors.reset p value K s 1 x=(value 1 ((Stationary.arm G f 1).symm x)).part s.val := by
  let K:=(caliber q earned.1).back depth
  let U (d:ℕ) (z:Stationary.Link G f):=(value d z).part s.val
  have smooth:∀d≤p,Differentiable ℝ (U d):=by
    intro d hd
    change Differentiable ℝ (fun z=>(value d z).part s.val)
    simp_rw [full d hd]
    exact copied multiple M w L T v d s.val
  exact ⟨WilsonThermometerOriginalClockSlope.zeroth U K p _,
    WilsonThermometerOriginalClockSlope.first U K (WilsonThermometerOriginalClockSlope.rating q a earned depth)
      p live smooth _⟩

end YM.Integration.WilsonThermometerOriginalDepositedSlope
