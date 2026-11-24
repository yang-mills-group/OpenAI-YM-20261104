import YM.Integration.WilsonMatrixOriginalGermNearFields
import YM.Integration.WilsonMatrixOriginalGermSlabCalendar
import YM.Integration.WilsonMatrixOriginalGermTestQuadrature
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! The full centered physical panel and its two-copy second moment are
paid uniformly over every original period in a growing range of UV dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSlabBudget
open Filter Lattice Wilson RG Spec Table RG17 OPE.Therm PhysicalNext.Repeat.Legato FVA2
open Extra.Multi.BasisCost Next.UVStress Trace.Pilot
open WilsonMatrixOriginalGermConditionalMask WilsonMatrixOriginalGermNearFields
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Spec.Final R.family f S) (L:Layout F)
local notation:max "β" i:arg => R.family.path.levels.clock.hatBeta i

theorem polynomial (e:ℕ) (M:Fin 2→ℝ) (mp:∀i,0≤M i) (φ:Test 2):
    ∃A:ℝ,0<A ∧ ∀(r:ℝ) (hr:0<r) (N p:ℕ) (w:Fin 2→R.family.label 4)
      (_age:R.family.ref 4≤L.level r) (live:L.level r≤N),R.family.S.a N≤r →
      R.family.S.a (L.level r)/R.family.S.a N≤β (L.level r) → β N≤β (L.level r)^2 →
      (∀i,quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) (w i)) ≤
        R.family.S.a (L.level r)^4*(β (L.level r)^e*M i)) →
      cost R (p:=p) (le_refl (L.level r)) live (fun i=>atRef L 4 r (N,p) (w i)) (dilate hr φ)
        ≤ A*β (L.level r)^(2*exponent R e):=by
  obtain ⟨mass,nm,mesh⟩:=WilsonMatrixOriginalGermTestQuadrature.uniform R φ
  let c:=price (R.family.localSection 4)
  let A:=mass*(6*(c*c)*(M 0*M 1))
  have nc:0≤c:=zero_le_one.trans (price_pos _)
  refine ⟨max 1 A,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
  intro r hr N p w age live small width heat paid
  have h:=joint R F L r mp w age le_rfl live width heat paid (dilate hr φ)
  have nb:0≤β (L.level r):=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  calc
    _ ≤ _:=h
    _ ≤ mass*(6*(cap R (L.level r) e (M 0)*cap R (L.level r) e (M 1))):=by
      apply mul_le_mul_of_nonneg_right (mesh r hr N p small)
      unfold cap
      positivity [nc,mp 0,mp 1]
    _ = A*β (L.level r)^(2*exponent R e):=by
      unfold A cap c; rw [two_mul,pow_add];ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg nb _)

theorem currency (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (wb:0<B)
    {g:ℝ→ℝ} (coupling:Coupling G g) (e:ℕ) (M:Fin 2→ℝ) (mp:∀i,0≤M i) (φ:Test 2):
    let stop:=WilsonMeasuredWindow.stop R.family.path.levels simple B
    ∃H:ℕ→ℕ,Tendsto H atTop atTop ∧ ∀(q:ℕ) (ε:ℝ),0<ε → ∃δ>0,∀ᶠr in trail,
      ∀(hr:0<r) (_clock:L.level r=stop r) (N p:ℕ) (w:Fin 2→R.family.label 4)
      (live:L.level r≤N), N≤L.level r+H (L.level r) →
      (∀i,quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) (w i)) ≤
        R.family.S.a (L.level r)^4*(β (L.level r)^e*M i)) →
      cost R (p:=p) (le_refl (L.level r)) live (fun i=>atRef L 4 r (N,p) (w i)) (dilate hr φ)*
        (δ*(g r)^(q+2*(2*exponent R e)))≤ε*(g r)^q:=by
  intro stop
  obtain ⟨H,growing,slab⟩:=WilsonMatrixOriginalGermSlabCalendar.growing R simple
  obtain ⟨A,ap,cash⟩:=polynomial R F L e M mp φ
  let d:=2*exponent R e
  have dp:0<(2:ℝ)^d:=by positivity
  refine ⟨H,growing,?_⟩
  intro q ε ep
  let δ:=ε/(A*2^d)
  have delta:0<δ:=div_pos ep (mul_pos ap dp)
  refine ⟨δ,delta,?_⟩
  have grows:Tendsto stop trail atTop:=WilsonMeasuredWindow.stop_tendsto _ simple B wb
  have hot:=(WilsonPhysicalCutoffCurrency.temperature R simple pace wb g coupling).eventually
    (gt_mem_nhds (show (1:ℝ)<2 by norm_num))
  filter_upwards [grows.eventually slab,grows.eventually_ge_atTop (R.family.ref 4),hot,coupling.positive]
    with r span old heat gp
  intro hr clock N p w live upper paid
  rw [←clock] at span old
  have bounds:=span N live upper
  have heat':β (L.level r)*(g r)^2 ≤ 2:=by simpa only [clock] using heat.le
  have room:R.family.S.a (L.level r)≤r:=by
    rw [clock]
    apply le_trans _ (WilsonMeasuredWindow.stop_spec R.family.path.levels simple B hr)
    exact le_mul_of_one_le_right (R.family.S.a_pos _).le (one_le_pow₀ (WilsonMeasuredAdmission.mast_gt_one _ _).le)
  have used:=cash r hr N p w old live ((R.family.S.strictAnti.antitone live).trans room) bounds.1 bounds.2 paid
  have nb:0≤β (L.level r):=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have convert:β (L.level r)^d*((g r)^2)^d≤2^d:=by
    rw [←mul_pow];exact pow_le_pow_left₀ (mul_nonneg nb (sq_nonneg _)) heat' _
  calc
    _ ≤ (A*β (L.level r)^d)*(δ*(g r)^(q+2*d)):=mul_le_mul_of_nonneg_right used
      (mul_nonneg delta.le (pow_nonneg gp.le _))
    _ = (A*δ)*(β (L.level r)^d*((g r)^2)^d)*(g r)^q:=by rw [pow_add,pow_mul];ring
    _ ≤ (A*δ)*2^d*(g r)^q:=by gcongr
    _ = _:=by dsimp [δ];field_simp

end YM.Integration.WilsonMatrixOriginalGermSlabBudget
