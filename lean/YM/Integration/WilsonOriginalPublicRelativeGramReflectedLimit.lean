import YM.Integration.WilsonOriginalPublicRelativeGramReporting
import YM.Integration.WilsonOriginalPublicRelativeGramOrientationLimit

/-! First use each original physical extraction on its booked real reporter.
Then let the physical zoom decrease. The R-family readings at the two honest
lattice sites retain every original source on this before-inversion filter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramReflectedLimit
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonPositionProgramPublicWickGram (vertex)
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

def ordered {A Z:Type}(outer:Filter A)(inner:A→Filter Z):Filter (A×Z):=
  outer.bind fun a=>(inner a).map (Prod.mk a)

theorem passage {A Z V:Type}[PseudoMetricSpace V]{out:Filter A}{inside:A→Filter Z}
    (val:A×Z→V)(reported:A→V){final:V}
    (inner:∀ᶠ a in out,Tendsto (fun z=>val (a,z)) (inside a) (𝓝 (reported a)))
    (outer:Tendsto reported out (𝓝 final)):
    Tendsto val (ordered out inside) (𝓝 final):=by
  apply Metric.tendsto_nhds.mpr
  intro e ep
  have e2:0<e/2:=half_pos ep
  change ∀ᶠ a in out,∀ᶠ z in inside a,dist (val (a,z)) final<e
  filter_upwards [inner,Metric.tendsto_nhds.mp outer (e/2) e2] with a read approx
  filter_upwards [Metric.tendsto_nhds.mp read (e/2) e2] with z small
  exact lt_of_le_of_lt (dist_triangle _ (reported a) _) (by linarith only [small,approx])

variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "I" => Glyph B h
local notation "P" => named R B h
local notation "ω" => (fun (r:ℝ) (_:Unit)=>ports R avoid (pointsAt a) (Γ.date r) r)
local notation "one" => (fun _:Unit=>(1:ℂ))
local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

def entered (Y:ℝ→(ℕ×ℕ)→I→R.family.label h)(p:ℝ×(ℕ×ℕ)):Matrix I I ℂ:=
  cutoff R a (fun _:I=>h) (Γ.date p.1) (ω p.1) one (fun _=>Y p.1) false p.2

theorem physical (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)(i j:I):
    Tendsto (fun r=>matrix R F a (fun _:I=>h) J (fun k=>P k) r r (Γ.date r) (ω r) one false i j) trail
      (𝓝 (maxwell B h a i j)):=by
  let δ:=fun r=>R.family.S.a (Γ.date r)/r
  have positive:∀ᶠ r in trail,0<r:=self_mem_nhdsWithin
  have dp:∀ᶠ r in trail,0<δ r:=positive.mono fun r rp=>div_pos (R.family.S.a_pos _) rp
  have fine:Tendsto δ trail (𝓝 0):=squeeze_zero' (dp.mono fun _ n=>n.le) Γ.upper
    (by simpa only [zero_pow (by decide:2≠0)] using (Coupling.conforms simple temperature).pow 2)
  have pos:vertex a≠-(vertex a):=by
    intro eq
    have bad:=congrArg norm ((WilsonPositionProgramPublicWickGram.apart a).symm.trans (sub_eq_zero.mpr eq))
    simp [basis_norm] at bad
  have result:=WilsonOriginalPublicRelativeGramLeading.original R F a (fun _:I=>h) J (fun k=>P k)
    id Γ.date ω (fun _=>one) (fun r _=>shape avoid (pointsAt a) (δ r)) (fun _=>pointsAt a) one
    lead tendsto_id (positive.mono fun r rp _=>WilsonOriginalPublicRelativeGramAddresses.placed R avoid
      (pointsAt a) (Γ.date r) rp) (fun _=>WilsonOriginalPublicRelativeGramAddresses.limit avoid (pointsAt a) dp fine)
    (fun _=>Extra.FD.couple_ok (Ne.symm pos)) (fun _=>tendsto_const_nhds) i j
  simpa [WilsonOriginalPublicRelativeGramLeading.free,incidence,maxwell] using result

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (Y:ℝ→(ℕ×ℕ)→I→R.family.label h)(b:ℝ→I→R.family.label h)
    (selected:∀ᶠr in trail,(∀i,Tendsto (fun z=>Y r z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b r i))) ∧
       ∀i,S.project h (b r i)=J r h (P i)):
    Tendsto (entered B h a R F ℓ avoid Γ Y) real (𝓝 (maxwell B h a)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  refine passage _ _ ?_ (physical B h a R F J ℓ avoid Γ simple temperature lead i j)
  filter_upwards [selected,(self_mem_nhdsWithin:∀ᶠr in trail,0<r)] with r tab rp
  exact WilsonOriginalPublicRelativeGramPins.limit R F a (fun _:I=>h) J (fun k=>P k) r r
    (Γ.date r) (ω r) one (fun _=>Y r) (fun _=>b r) (fun _ k=>tab.1 k) (fun t k=>by cases t <;> exact tab.2 k)
    below (fun _ _=>WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) (Γ.date r) rp) false i j

end YM.Integration.WilsonOriginalPublicRelativeGramReflectedLimit
