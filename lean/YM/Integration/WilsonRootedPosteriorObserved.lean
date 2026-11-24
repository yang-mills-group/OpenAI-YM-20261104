import YM.Integration.WilsonRootedPosteriorConnected

/-! The same complete physical signed array under the original conditional
probability, with one true coarse normalization in all three terms. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorObserved
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Pressure Pressure.Testing Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonRootedPosteriorDifferences (law relative)
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level

def slot (incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode):Config G fine→ℂ:=relative R d (Actual.atMark s incoming)
def raw (V:Config G coarse)(w:Config G fine→ℝ)(incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode)(t:ℂ):ℂ:=
  (Δ).push (P).beta (fun U=>Complex.exp (t*(w U:ℂ))*Actual.atMark s incoming U) V
def effect (V:Config G coarse)(w:Config G fine→ℝ)(incoming:Actual.Lit Γ (Config G fine))(a b:I)
    (legal:({a,b}:Finset I)∈Γ.choices)(t:ℂ):ℂ:=
  let y:=raw R d V w incoming
  y ⟨{a,b},legal⟩ t/y Γ.quiet t -(y (Γ.fire a) t/y Γ.quiet t)*(y (Γ.fire b) t/y Γ.quiet t)
def row (incoming:Actual.Lit Γ (Config G fine))(a b:I)(legal:({a,b}:Finset I)∈Γ.choices)
    (X:Config G coarse×Config G fine):ℂ:=
  let r:=slot R d incoming
  WilsonRootedPosteriorConnected.test (law R d X.1) (r (Γ.fire a)) (r (Γ.fire b)) (r ⟨{a,b},legal⟩) X.2

theorem original (V:Config G coarse)(w:Config G fine→ℝ)(pw:Envelope w)(incoming:Actual.Lit Γ (Config G fine))
    (floor:Actual.Floor P incoming)(a b:I)(legal:({a,b}:Finset I)∈Γ.choices):
    HasDerivAt (effect R d V w incoming a b legal) (∫U,(w U:ℂ)*row R d incoming a b legal (V,U) ∂law R d V) 0:=by
  let μ:=law R d V
  let r:=slot R d incoming
  let e:=WilsonRootedPosteriorConnected.variation μ w
  let J:Γ.Mode:=⟨{a,b},legal⟩
  let z:=((P₀).eval V:ℂ)
  have pos:z≠0:=Complex.ofReal_ne_zero.mpr ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive V).ne'
  have seen (s:Γ.Mode)(t:ℂ):raw R d V w incoming s t=z*e (r s) t:=by
    have receipt:=WilsonRootedPosteriorDifferences.tilted R d V (fun U=>Complex.exp (t*(w U:ℂ))) (Actual.atMark s incoming)
    change e (r s) t=raw R d V w incoming s t/z at receipt
    rw [receipt]
    field_simp
  have zero:r Γ.quiet=fun _=>1:=by
    funext U
    change (incoming U).part Γ.quiet/((P).eval U:ℂ)=1
    rw [floor.vacancy U,div_self (Complex.ofReal_ne_zero.mpr
      ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U).ne')]
  have cancel (x y:ℂ):(z*x)/(z*y)=x/y:=by
    by_cases h:y=0
    · simp [h]
    · field_simp
  have real:effect R d V w incoming a b legal=WilsonRootedPosteriorConnected.response μ w (r (Γ.fire a)) (r (Γ.fire b)) (r J):=by
    funext t
    unfold effect WilsonRootedPosteriorConnected.response
    simp only [seen,cancel,zero]
    rfl
  rw [real]
  letI:IsProbabilityMeasure μ:=WilsonRootedPosteriorDifferences.probability R d V
  have env (s:Γ.Mode):Envelope (r s):=WilsonRootedPosteriorDifferences.admissible R d _ (floor.safe s)
  exact WilsonRootedPosteriorConnected.sweep μ w _ _ _ pw (env _) (env _) (env _)

theorem copies (V:Config G coarse)(w:Config G fine→ℝ)(pw:Envelope w)(incoming:Actual.Lit Γ (Config G fine))
    (floor:Actual.Floor P incoming)(a b:I)(legal:({a,b}:Finset I)∈Γ.choices)(s:ℂ):
    (deriv (effect R d V w incoming a b legal) 0=
      ∫U,((w U:ℂ)-s)*row R d incoming a b legal (V,U) ∂law R d V) ∧
    2*deriv (effect R d V w incoming a b legal) 0=
      WilsonRootedPosteriorDifferences.oscillation (law R d V) (fun U=>(w U:ℂ)) (fun U=>row R d incoming a b legal (V,U)):=by
  let r:=slot R d incoming
  let μ:=law R d V
  letI:IsProbabilityMeasure μ:=WilsonRootedPosteriorDifferences.probability R d V
  have env (i:Γ.Mode):Envelope (r i):=WilsonRootedPosteriorDifferences.admissible R d _ (floor.safe i)
  rw [(original R d V w pw incoming floor a b legal).deriv]
  exact ⟨(WilsonRootedPosteriorConnected.subtract μ (fun U=>(w U:ℂ)) _ _ _ pw.ofReal_env (env _) (env _) (env _) s).symm,
    (WilsonRootedPosteriorConnected.copies μ _ _ _ _ pw.ofReal_env (env _) (env _) (env _)).symm⟩

end YM.Integration.WilsonRootedPosteriorObserved
