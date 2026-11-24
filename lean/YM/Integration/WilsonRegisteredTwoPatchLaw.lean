import YM.Integration.WilsonRegisteredTwoPatchHaar
import YM.Integration.WilsonRegisteredExteriorSeries

/-! The fitted earlier law over two regions disintegrates into the true first
region's original conditional at the sampled exterior and its actual random
mass in the remaining Haar integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredTwoPatchLaw
open Function MeasureTheory Lattice RG Wilson OriginalMarkedRowCovariance WilsonHeldRetainedAction
open PhysicalNext.Repeat.Legato OriginalMarkedRunAction Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open private kernel_env kernel_floor from YM.Integration.WilsonHeldExteriorLaw
open private paid_mass from YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact
open scoped Classical
variable {G:Gauge}(R:Run G){m N per r:ℕ}{Z:SeriesA G}{σ C ε:ℝ}
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "P" => R.family.path.rep N per (m+1)
local notation "K" => StepData.density (R.family.path.levels.clock.op m per) (R.family.path.β N per (m+1))
local notation "η" => prior G (R.family.side (m+1) per)
local notation "ξ" => OriginalMarkedConditionalAction.patch

def density (Z:SeriesA G)(σ C:ℝ)(W:coarse)(u:fine):ℝ:=K u W*maskedSpringWeight R (N:=N) r Z σ C u

set_option backward.isDefEq.respectTransparency false in
theorem finite (live:m+1≤N)(osc:LocalSpringOscillation R m N per r Z σ C ε)(W:coarse):
    Envelope (density R (N:=N) (r:=r) Z σ C W) ∧ ∀u,0<density R (N:=N) (r:=r) Z σ C W u:=by
  let D:=maskedSpringScore R N per (m+1) r Z σ C
  let sites:Support (R.family.side (m+1) per):=Finset.univ
  let upper:=ε*sites.card*(regulatorRun R.family N per (m+1))^2/(2*Real.exp 2)
  have univ (u:fine):ξ sites 1 u=u:=by funext e;simp [sites,OriginalMarkedConditionalAction.patch]
  have paid(u:fine):|D u-D 1|≤upper:=by
    simpa only [springLocalChange,univ] using (spring_prior_bounds R osc sites 1).2 u
  have ed:Envelope (fun u=>Real.exp (D u)):=⟨osc.1.exp,Real.exp (D 1+upper),fun u=>by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    linarith [(abs_le.mp (paid u)).2]⟩
  have pk:=kernel_env (R.family.path.levels.clock.op m per) (R.family.path.β N per (m+1))
    (R.family.path.levels.blocks m per).branches W
  have pp:Envelope (P).eval:=(P).envelope (R.makes.wilson.represents N per (m+1) live).good
  obtain ⟨a,ap,below⟩:=kernel_floor R N per m live
  have same:density R (N:=N) (r:=r) Z σ C W=(fun u=>K u W*(Real.exp (D u)*(P).eval u)):=by
    funext u;exact congrArg _ (spring_tilt R r Z σ C u)
  rw [same]
  exact ⟨pk.mul (ed.mul pp),fun u=>mul_pos (ap.trans_le (below u W))
    (mul_pos (Real.exp_pos _) (Multi.AxisShift.chosen_positive R.makes.wilson live u))⟩

set_option backward.isDefEq.respectTransparency false in
theorem row (live:m+1≤N)(S:Support (R.family.side (m+1) per))(ext:fine)(W:coarse)(f:fine→ℂ):
    WilsonRegisteredExteriorSeries.tilted R (N:=N) (r:=r) Z σ C S f (W,ext)=
      WilsonRegisteredTwoPatchHaar.row S ext (density R (N:=N) (r:=r) Z σ C W) f:=by
  have pk:=kernel_env (R.family.path.levels.clock.op m per) (R.family.path.β N per (m+1))
    (R.family.path.levels.blocks m per).branches W
  have ek:Envelope (fun u=>K (ξ S ext u) W):=by
    obtain ⟨c,pay⟩:=pk.cost
    exact ⟨pk.meas.comp (OriginalMarkedConditionalAction.measurable_patch S ext),c,fun u=>pay _⟩
  obtain ⟨a,ap,low⟩:=kernel_floor R N per m live
  letI:IsProbabilityMeasure η:=inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Edge (Site (R.family.side (m+1) per))=>G.probHaar)))
  have pos(u:fine):0<K (ξ S ext u) W:=ap.trans_le (low _ W)
  exact WilsonRegisteredExteriorNormalization.weighted η _ _ _ ek.meas (fun u=>(pos u).le) (paid_mass η ek pos)

set_option backward.isDefEq.respectTransparency false in
theorem original (live:m+1≤N)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S T:Support (R.family.side (m+1) per))(ext:fine)(W:coarse)(f:fine→ℂ)(ef:Envelope f):
    let z(t:fine):=WilsonRegisteredTwoPatchHaar.mass S (ξ T ext t) (density R (N:=N) (r:=r) Z σ C W)
    let inner(t:fine):=WilsonRegisteredExteriorSeries.tilted R (N:=N) (r:=r) Z σ C S f (W,ξ T ext t)
    (∀t,0<z t) ∧ WilsonRegisteredExteriorSeries.tilted R (N:=N) (r:=r) Z σ C (S∪T) f (W,ext)=read η z inner:=by
  intro z inner
  obtain ⟨ew,pos⟩:=finite R live osc W
  letI:IsProbabilityMeasure η:=inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Edge (Site (R.family.side (m+1) per))=>G.probHaar)))
  constructor
  · intro t
    let x:=ξ T ext t
    have eg:Envelope (fun s=>density R (N:=N) (r:=r) Z σ C W (ξ S x s)):=by
      obtain ⟨c,h⟩:=ew.cost
      exact ⟨ew.meas.comp (OriginalMarkedConditionalAction.measurable_patch S x),c,fun u=>h _⟩
    exact paid_mass η eg (fun u=>pos _)
  · have eq (t:fine):inner t=WilsonRegisteredTwoPatchHaar.row S (ξ T ext t) (density R (N:=N) (r:=r) Z σ C W) f:=row R live _ _ _ _
    rw [row R live]
    change _=read η z (fun t=>inner t)
    simp_rw [eq]
    exact WilsonRegisteredTwoPatchHaar.original S T ext _ f ew pos ef
end YM.Integration.WilsonRegisteredTwoPatchLaw
