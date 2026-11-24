import YM.Integration.WilsonMatrixTicketLanesRegisteredValue
import YM.Integration.WilsonMatrixTicketLanesRegisteredWard
import YM.Integration.WilsonInvariantActionExponentialHearing

/-! The genuine nonzero filed Ward row and its five changed-vacuum terms
on one original regulated covariance, with a separate signed wave at each layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredTilt
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG17 Spec
open Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics RGComparison.Core16
open WilsonInvariantActionCapturedProfile WilsonMatrixOriginalReportingMargin
open WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
open WilsonMatrixTicketLanesRegisteredHearing
open private zero unit from YM.Integration.WilsonInvariantActionExponentialHearing
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {k N per:ℕ}
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "lower" => Config G (R.family.side k per)
local notation "Ω" => (lower × upper)
local notation "Sites" => (Fin 2 → Site (R.family.side N per))

def full (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (marks:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (w:Sites → readings Ω) (t:ℝ):ℝ:=
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  panel R live birth marks φ χ fun x=>covariance (WilsonInvariantActionExponentialHearing.normalized R live (w x) t)

def paid (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (marks:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (w:Sites → readings Ω):ℝ:=
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  panel R live birth marks φ χ fun x A B=>receipts R live A B (w x)

theorem measured (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (marks:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (w:Sites → readings Ω):
    full R inside birth marks φ χ w 0=χ (WilsonInvariantActionCapturedProfile.earlier R (per:=per) inside.le marks φ) ∧
      HasDerivAt (full R inside birth marks φ χ w) (paid R inside birth marks φ χ w) 0:=by
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  have normalizedUnit:joint R (p:=per) live 1=1:=unit R live
  constructor
  · have initial:=WilsonMatrixTicketLanesRegisteredValue.original R (per:=per) inside birth marks φ χ (fun _=>0)
    calc
      _=variation R (per:=per) inside birth marks φ χ (fun _=>0) 0:=by
        apply congrArg (WilsonMatrixTicketLanesRegisteredHearing.panel R live birth marks φ χ)
        funext x A B
        simp only [covariance,WilsonInvariantActionExponentialHearing.normalized,zero,normalizedUnit,
          reweighted,zero_mul,add_zero,div_one]
      _=_:=initial
  · unfold full paid WilsonMatrixTicketLanesRegisteredHearing.panel
    apply HasDerivAt.fun_sum
    intro x _
    let o:=fun i=>(R.family.S.toDepth live per).parent (x i)
    have arm(η θ:ℂ →L[ℝ]ℝ):=WilsonInvariantActionExponentialHearing.original R live
      (filed R live birth (marks 0) (o 0) η) (filed R live birth (marks 1) (o 1) θ) (w x)
    let c:=WilsonExternalMeshMass.charge R.family φ x
    exact (((arm _ _).sub (arm _ _)).const_mul (χ c)).add (((arm _ _).add (arm _ _)).const_mul (χ (c*Complex.I)))

variable {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S) (L:Layout F) {U:Filter (ℕ×ℕ)}

def Response (a b:ℝ → R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ →L[ℝ]ℝ) (σ:ℝ):Prop:=
  ∀ cap:ℕ,∀ ε>0,∀ᶠ r in trail,∀ hr:0<r,∀ᶠ z:ℕ×ℕ in U,
    ∃ k,∃ date:L.level r=k+1,∃ inside:k+1<z.1,∃ birth:R.family.ref 4 ≤ k+1,
    let v:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let future:L.level r≤z.1:=date.trans_le inside.le
    ∀ w:(Fin 2 → Site (R.family.side z.1 z.2)) → readings
        (Config G (R.family.side k z.2) × Config G (R.family.side (k+1) z.2)),
      HasDerivAt (full R inside birth v (dilate hr φ) χ w) (paid R inside birth v (dilate hr φ) χ w) 0 ∧
      ∀u:Directions G (R.family.side k z.2),(∀i,‖u i‖≤(cap:ℝ)+1) →
        let fresh:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future u
        let difference:=full R inside birth v (dilate hr φ) χ w 0-χ fresh
        |difference-χ c|≤‖χ‖*ε ∧ |χ c|/4<σ*difference

theorem original (a b:ℝ → R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ →L[ℝ]ℝ) (σ:ℝ)
    (grows:Tendsto L.level trail atTop)
    (actual:WilsonMatrixTicketLanesConnectedMargin.Remaining (U:=U) R F L a b φ c χ σ):
    Response (U:=U) R F L a b φ c χ σ:=by
  intro cap ε ep
  filter_upwards [actual cap ε ep,grows.eventually_ge_atTop (R.family.ref 4)] with r earlier age
  intro hr
  filter_upwards [earlier hr] with z coverage
  obtain ⟨k,date,future,holds⟩:=coverage
  have birth:R.family.ref 4 ≤ k+1:=date ▸ age
  have inside:k+1<z.1:=date ▸ future
  refine ⟨k,date,inside,birth,?_⟩
  let v:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let old:=WilsonInvariantActionCapturedProfile.earlier R (per:=z.2) inside.le v (dilate hr φ)
  dsimp only []
  intro w
  have both:=measured R inside birth v (dilate hr φ) χ w
  refine ⟨both.2,?_⟩
  intro u pinned
  let bare:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future.le u
  have buy:‖old-bare-c‖≤ε ∧ |χ c|/4<σ*χ (old-bare):=by
    simpa only [old,date] using holds u pinned
  change |full R inside birth v (dilate hr φ) χ w 0-χ bare-χ c|≤‖χ‖*ε ∧
    |χ c|/4<σ*(full R inside birth v (dilate hr φ) χ w 0-χ bare)
  rw [both.1]
  change |χ old-χ bare-χ c|≤‖χ‖*ε ∧ |χ c|/4<σ*(χ old-χ bare)
  rw [←map_sub,←map_sub]
  exact ⟨(χ.le_opNorm _).trans (mul_le_mul_of_nonneg_left buy.1 (norm_nonneg _)),buy.2⟩

end YM.Integration.WilsonMatrixTicketLanesRegisteredTilt
