import YM.Integration.WilsonOriginalTwoFlatPublicPanel
import YM.Integration.WilsonOriginalTwoFlatCompact
import YM.Integration.WilsonOriginalTwoFlatTelescope

/-! Join the issued reflected phase comparison to both older flat reports
of the same actual public numerator. The independent compact is freshly
submitted with its native regular and global wages on the original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicStops
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology

open MeasureTheory MergeProof Ribbons Accent OPE Bid WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatTelescope (entrance interval)
open WilsonOriginalTwoFlatGridScaling (gap)
variable {G:Gauge}(R:Run G){N per c u v K:ℕ}
local notation "C" => R.family
local notation "rep" => (C).path.rep N per c
local notation "Sec" => (C).localSection 0
local notation "μ" => price G (max (rep).p.order (rep).p.power)
local notation "κ" => LocalComparison.forcedDivisor C c
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance c
local notation "Q" j:max => Config G ((C).side j per)

def debt {z:ℕ}(Y:Cut C N per)(zK:z ≤ K)(kn:K ≤ N)(M:∀i:ℕ,(Q i)→ℂ)(c:ℕ):ℝ:=
  entrance R Y zK kn M+∑i∈Ico c K,‖feeAt R N per z M i‖

private theorem restore {z:ℕ}(zc:z ≤ c)(ck:c ≤ K)(kn:K ≤ N)(Y:Cut C N per)(hc:Continuous Y)
    (M:∀i:ℕ,(Q i)→ℂ)(paid:∀i,c ≤ i → i ≤ K → Integrable (numerator R N per i (M i)) (prior G _)):
    ‖reading R (N:=N) (credit C N per 0 Y c (ck.trans kn)) z zc-
      reading R (N:=N) (numerator R N per c (M c)) z zc‖  ≤  debt R Y (zc.trans ck) kn M c:=by
  unfold debt
  have same:reading R (N:=N) (credit C N per 0 Y c (ck.trans kn)) z zc=
      reading R (N:=N) (credit C N per 0 Y K kn) z (zc.trans ck):=by
    unfold reading
    rw [cutoff R (ck.trans kn) zc Y hc,cutoff R kn (zc.trans ck) Y hc]
  rw [same]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (reading R (N:=N) (numerator R N per K (M K)) z (zc.trans ck)) _).trans ?_
  rw [interval R zc ck kn M paid]
  exact add_le_add (le_refl _) (norm_sum_le (Ico c K) (fun j=>feeAt R N per z M j))

theorem actual (simple:G.Simple)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(kn:K ≤ N)(cN:c<N)
    (ou:Opened C 0 u per)(ov:Opened C 0 v per)(ready:WilsonCenteredCaptureClock.first R simple ≤ c)
    (Y:Cut C N per)(hc:Continuous Y)(A:ℝ)(reflected:‖gap R N per u (((uv.trans vc).trans ck).trans kn) Y‖ ≤ A)
    (M:∀i:ℕ,(Q i)→ℂ)(paid:∀i,c ≤ i → i ≤ K → Integrable (numerator R N per i (M i)) (prior G _))
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:(rep).p=p)
    (x:X)(s:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈s.val,o a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (o a) 0 ≤ rad)(w:V→ℝ)(wp:∀a,0<w a)
    {derivative gross:ℝ}(he:L.Paid w p.B (p.supportExponent+2) derivative)
    (hg:Gross L w p.B (p.supportExponent+2) gross)
    (placed:M c=fun U=>(Poly.pass (bare L x U)).part s):
    let fee:=WilsonPlantedOrdinary.fare (rep).p Z w derivative gross rad (Sec) (C).params μ v₀ κ s
    ‖gap R N per v ((vc.trans ck).trans kn) Y‖  ≤  A+debt R Y ((uv.trans vc).trans ck) kn M c+
      2*capital C c fee 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8)+debt R Y (vc.trans ck) kn M c:=by
  have compact:=WilsonOriginalTwoFlatCompact.original R simple ou.post uv vc cN ou ov ready
    L same x s Z center reside rad near w wp he hg
  have equal:numerator R N per c (M c)=fun U=>((rep).eval U:ℂ)*(Poly.pass (bare L x U)).part s:=by
    rw [placed];rfl
  rw [←equal] at compact
  let native:=credit C N per 0 Y c cN.le
  let source:=numerator R N per c (M c)
  have same {z:ℕ}(zc:z ≤ c):reading R (N:=N) native z zc=reading R (N:=N) (credit C N per 0 Y z (zc.trans cN.le)) z le_rfl:=by
    unfold reading;rw [cutoff R cN.le zc Y hc,gust_base]
  have first:‖(C).omega N per Y-reading R (N:=N) native u (uv.trans vc)‖ ≤ A:=by
    rw [same];exact reflected
  change ‖(C).omega N per Y-reading R (N:=N) (credit C N per 0 Y v _) v le_rfl‖  ≤  _
  rw [←same vc]
  have fixed:=restore R (uv.trans vc) ck kn Y hc M paid
  have moving:=restore R vc ck kn Y hc M paid
  let top:=(C).omega N per Y
  let a₁:=reading R (N:=N) native u (uv.trans vc)
  let a₂:=reading R (N:=N) source u (uv.trans vc)
  let a₃:=reading R (N:=N) source v vc
  let a₄:=reading R (N:=N) native v vc
  have span:‖top-a₄‖  ≤  ((‖top-a₁‖+‖a₁-a₂‖)+‖a₂-a₃‖)+‖a₄-a₃‖:=by
    calc
      _  ≤  ‖top-a₃‖+‖a₄-a₃‖:=by simpa only [norm_sub_rev a₃ a₄] using norm_sub_le_norm_sub_add_norm_sub top a₃ a₄
      _ ≤ _:=add_le_add ((norm_sub_le_norm_sub_add_norm_sub top a₂ a₃).trans
        (add_le_add (norm_sub_le_norm_sub_add_norm_sub top a₁ a₂) (le_refl _))) (le_refl _)
  exact span.trans (add_le_add (add_le_add (add_le_add first fixed) compact) moving)

end YM.Integration.WilsonOriginalTwoFlatPublicStops
end
