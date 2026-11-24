import YM.Integration.WilsonRootedNonflatAllSectors
import YM.Integration.WilsonRootedNonflatPreviousCost
import YM.Integration.WilsonRootedNonflatExponential

/-! The actual exponential score of one complete filed previous site
in the original signed joint logarithmic numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatPreviousResponse
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonRootedNonflatPreviousCost (letter bill)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "w" => R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)
local notation "E" => Gaussian.Vec (Raw G coarse)

def ink (r:ℕ)(Z:SeriesA G)(o:Site fine)(u:Config G fine→ℂ)(U:Config G fine):ℂ:=
  (letter R d r Z o U:ℂ)*u U

def swept (V:Config G coarse)(r:ℕ)(Z:SeriesA G)(o:Site fine)(incoming:Actual.Lit Γ (Config G fine))
    (s:Γ.Mode)(t:ℂ):ℂ:=
  (Δ).push (P).beta (fun U=>Complex.exp (t*(letter R d r Z o U:ℂ))*Actual.atMark s incoming U) V

def pair (V:Config G coarse)(r:ℕ)(Z:SeriesA G)(o:Site fine)(incoming:Actual.Lit Γ (Config G fine))
    (a b:I)(legal:({a,b}:Finset I)∈Γ.choices)(t:ℂ):ℂ:=
  let y:=swept R d V r Z o incoming
  y ⟨{a,b},legal⟩ t/y Γ.quiet t-(y (Γ.fire a) t/y Γ.quiet t)*(y (Γ.fire b) t/y Γ.quiet t)

def score (z:ℂ)(full old:Γ.Mode→ℂ)(a b:I)(legal:({a,b}:Finset I)∈Γ.choices):ℂ:=
  let ab:Γ.Mode:=⟨{a,b},legal⟩
  old ab/z-(old Γ.quiet*full ab+old (Γ.fire a)*full (Γ.fire b)+old (Γ.fire b)*full (Γ.fire a))/z^2+
    2*old Γ.quiet*full (Γ.fire a)*full (Γ.fire b)/z^3

def mode (D:Allocation G Δ Θ w)(q:Chi)(B:E)(incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode):ℂ:=
  WilsonRootedNonflatAllSectors.reading R d D q B (Actual.atMark s incoming)

def prior (D:Allocation G Δ Θ w)(q:Chi)(B:E)(r:ℕ)(Z:SeriesA G)(o:Site fine)
    (incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode):ℂ:=
  WilsonRootedNonflatAllSectors.reading R d D q B (ink R d r Z o (Actual.atMark s incoming))

def Court (D:Allocation G Δ Θ w)(q:Chi)(B:E):Prop:=
  ∀(r:ℕ)(Z:SeriesA G){σ c:ℝ},0<σ→Draw Z σ c→∀(o:Site fine)(incoming:Actual.Lit Γ (Config G fine)),
    Actual.Floor P incoming→∀(a b:I)(legal:({a,b}:Finset I)∈Γ.choices),
      HasDerivAt (pair R d (represent (decode B)) r Z o incoming a b legal)
        (score (((P₀).eval (represent (decode B))):ℂ)
          (mode R d D q B incoming) (prior R d D q B r Z o incoming) a b legal) 0

theorem original (D:Allocation G Δ Θ w)(q:Chi):∀ᶠ B:E in 𝓝 0,Court R d D q B:=by
  filter_upwards [WilsonRootedNonflatAllSectors.original R d D q] with B hB
  intro r Z σ c hs hz o incoming floor a b legal
  let V:=represent (decode B)
  let y:=swept R d V r Z o incoming
  let x:=mode R d D q B incoming
  let e:=prior R d D q B r Z o incoming
  let J:Γ.Mode:=⟨{a,b},legal⟩
  have paid:=WilsonRootedNonflatPreviousCost.invoice R d r Z hs hz o
  have inv (s:Γ.Mode):GaugeInvariant (Actual.atMark s incoming):=
    fun h U=>congrArg (fun p:Poly Γ=>p.part s) (floor.gauges h U)
  have full (s:Γ.Mode):x s=(Δ).push (P).beta (Actual.atMark s incoming) V:=hB _ (floor.safe s) (inv s)
  have full0 (s:Γ.Mode):y s 0=x s:=by
    rw [full s]
    simp only [y,swept,zero_mul,Complex.exp_zero,one_mul]
  have dep (s:Γ.Mode):HasDerivAt (y s) (e s) 0:=by
    have gi:GaugeInvariant (ink R d r Z o (Actual.atMark s incoming)):=by
      intro h U
      unfold ink
      rw [paid.2.1 h U,inv s h U]
    have two:e s=(Δ).push (P).beta (ink R d r Z o (Actual.atMark s incoming)) V:=
      hB _ (paid.1.ofReal_env.mulC (floor.safe s)) gi
    rw [two]
    exact WilsonRootedNonflatExponential.pushed (R.family.path.levels.transition_mass d.level d.period (P).beta)
      V _ paid.1 _ (floor.safe s)
  have z:=WilsonRootedNonflatDye.quiet R d D q V (0:fieldDir G coarse 1) incoming floor
  have zero:x Γ.quiet=((P₀).eval V:ℂ):=by
    rw [full,←WilsonRootedNonflatLog.measured R d D q V (0:fieldDir G coarse 1) _ (floor.safe Γ.quiet) (inv Γ.quiet)]
    exact z.1
  have yes:y Γ.quiet 0≠0:=(full0 Γ.quiet).trans_ne (zero.trans_ne (Complex.ofReal_ne_zero.mpr z.2.ne'))
  have h:=WilsonRootedNonflatExponential.pair (dep Γ.quiet) (dep (Γ.fire a)) (dep (Γ.fire b)) (dep J) yes
  rw [full0 Γ.quiet,zero,full0 J,full0 (Γ.fire a),full0 (Γ.fire b)] at h
  exact h

theorem nonflat (D:Allocation G Δ Θ w)(q:Chi)(simple:G.Simple)(size:2≤(coarse).val){θ:ℝ}(ht:0<θ):
    ∃B:E,Court R d D q B ∧ flags θ (represent (decode B))=∅ ∧
      G.curvature (faceValue (represent (decode B)) (WilsonRootedHeldNonflat.selected (coarse)))≠0 ∧
      ∀{s:ℝ},s≠0→Integral.sample s (s⁻¹ • decode B)=represent (decode B):=
  WilsonRootedNonflatAppointment.original (coarse) simple size ht _ (original R d D q)

end YM.Integration.WilsonRootedNonflatPreviousResponse
