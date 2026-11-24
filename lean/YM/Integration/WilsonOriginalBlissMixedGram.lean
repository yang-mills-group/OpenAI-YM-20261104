import YM.Integration.WilsonOriginalBlissSimultaneousGram

/-! The signed complex response of two independent physical cutoff fields.
Both field vectors may vary on the original extraction filter and the two
held fields may be calibrated at different dates and grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissMixedGram
open Filter Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonPositionOriginalDiagnosticMeasuredGram WilsonOriginalBlissSimultaneousGram
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  (arch:Trace.Terrace.Arch R.family)(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
local notation "L"=>WilsonOriginalBlissObserved.layout F bliss J level shift

def grades (d e:ℕ):Fin 2→ℕ:=Fin.cons d (fun _=>e)

def columns (a:Axis)(d e:ℕ)(v:R.family.label d)(w:R.family.label e):
    R.family.book.Vector (grades d e):=
  Fin.cons (α:=fun i=>R.family.label (grades d e i)) (R.family.book.adj d a v) (fun _=>w)

def testPair (a:Axis)(d e:ℕ)(φ ψ:Test 1)
    (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x):Test 2:=
  withOther (oneTest R d a φ hp 0) (oneTest R e a ψ hq 0)

def price (a:Axis)(d e:ℕ)(φ ψ:Test 1)
    (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x)
    (v:S.Field d)(w:S.Field e):ℂ:=
  S.integralOn (grades d e) (columns R a d e (S.representative d v) (S.representative e w))
    (testPair R a d e φ ψ hp hq)

private theorem tags (a:Axis)(d e:ℕ)(φ ψ:Test 1)
    (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x)
    (v:R.family.label d)(w:R.family.label e):
    tied (oneTest R d a φ hp v).v (oneTest R e a ψ hq w).v a =
      fun i=>(⟨grades d e i,columns R a d e v w i⟩:R.family.book.Token):=by
  funext i
  fin_cases i <;> rfl


private theorem adjoint (a:Axis)(d:ℕ){b:Filter (ℕ×ℕ)} {x:ℕ×ℕ→R.family.label d}{v:R.family.label d}
    (hx:Tendsto x b (𝓝 v)):Tendsto (fun z=>R.family.book.adj d a (x z)) b (𝓝 (R.family.book.adj d a v)):=by
  change Tendsto (fun z=>(R.family.book.mirrorGroup d (Signed.mirror a)) (star (x z))) _ _
  exact (R.family.book.mirrorGroup d _).continuous_of_finiteDimensional.continuousAt.tendsto.comp hx.star

include F in
theorem cutoff (a:Axis)(d e:ℕ)(φ ψ:Test 1)
    (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x)
    {b:Filter (ℕ×ℕ)}[b.NeBot](below:b≤f.fuse)
    {x:ℕ×ℕ→R.family.label d}{y:ℕ×ℕ→R.family.label e}{v:R.family.label d}{w:R.family.label e}
    (hx:Tendsto x b (𝓝 v))(hy:Tendsto y b (𝓝 w)):
    Tendsto (fun z:ℕ×ℕ=>Cells.form (R.family.beta z.1 z.2) (plane R.family z.1 z.2 a)
      (stem R.family (oneTest R e a ψ hq (y z)) z.1 z.2) (stem R.family (oneTest R d a φ hp (x z)) z.1 z.2))
      b (𝓝 (S.integralOn (grades d e) (columns R a d e v w) (testPair R a d e φ ψ hp hq))):=by
  have adj:=adjoint R a d hx
  have buy:=Next.UVStress.calibrated_smear F.room.ordered b below (testPair R a d e φ ψ hp hq)
    (d:=grades d e) (v:=fun z=>columns R a d e (x z) (y z)) (x:=columns R a d e v w)
    (he:=by intro i; fin_cases i;exact adj;exact hy)
  have read:∀ᶠz:ℕ×ℕ in f.fuse,suitable R.family.S z.2 φ:=by
    change ∀ᶠp:ℕ in atTop,∀ᶠj:ℕ in atTop,suitable R.family.S (f.per p) φ
    filter_upwards [f.per.cofinal.eventually (reading R.family.S φ)] with p yes using Eventually.of_forall (fun _=>yes)
  apply buy.congr'
  filter_upwards [read.filter_mono below,(Next.UVStress.large_mesh f (R.family.ref d)).filter_mono below]
    with z placed active
  have same:=at_cut R.family (oneTest R d a φ hp (x z)) (oneTest R e a ψ hq (y z))
    (fun _=>active) placed R.makes
  rw [tags] at same
  exact same

include bliss J in
theorem original (a:Axis)(d e:ℕ)(r s:ℝ)(φ ψ:Test 1)
    (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x)
    (ref:R.family.ref d≤level r)(set:R.family.ref e≤level s)
    {V:ℕ×ℕ→S.Field d}{W:ℕ×ℕ→S.Field e}{v:S.Field d}{w:S.Field e}
    (hv:Tendsto V (l:Filter (ℕ×ℕ)) (𝓝 v))(hw:Tendsto W (l:Filter (ℕ×ℕ)) (𝓝 w)):
    Tendsto (fun z:ℕ×ℕ=>Cells.form (R.family.beta z.1 z.2) (plane R.family z.1 z.2 a)
      (field R F arch level shift e s ψ z (W z)) (field R F arch level shift d r φ z (V z)))
      (l:Filter (ℕ×ℕ)) (𝓝 (price R a d e φ ψ hp hq v w)):=by
  let x (z:ℕ×ℕ):=atRef L d r z (WilsonOriginalBlissFieldLift.column (S:=S) arch level shift d r (V z))
  let y (z:ℕ×ℕ):=atRef L e s z (WilsonOriginalBlissFieldLift.column (S:=S) arch level shift e s (W z))
  have h₁:Tendsto x (l:Filter (ℕ×ℕ)) (𝓝 (S.representative d v)):=by
    rw [← WilsonOriginalBlissFieldLift.located F arch bliss J level shift d r v]
    exact tendsRef L le_rfl (((WilsonOriginalBlissFieldLift.column (S:=S) arch level shift d r).continuous_of_finiteDimensional.tendsto _).comp hv) ref
  have h₂:Tendsto y (l:Filter (ℕ×ℕ)) (𝓝 (S.representative e w)):=by
    rw [← WilsonOriginalBlissFieldLift.located F arch bliss J level shift e s w]
    exact tendsRef L le_rfl (((WilsonOriginalBlissFieldLift.column (S:=S) arch level shift e s).continuous_of_finiteDimensional.tendsto _).comp hw) set
  simp_rw [WilsonOriginalBlissSimultaneousGram.literal R F arch bliss J level shift a d r φ hp,
    WilsonOriginalBlissSimultaneousGram.literal R F arch bliss J level shift a e s ψ hq]
  exact cutoff R F a d e φ ψ hp hq (b:=(l:Filter (ℕ×ℕ))) (L).certified h₁ h₂

end YM.Integration.WilsonOriginalBlissMixedGram
