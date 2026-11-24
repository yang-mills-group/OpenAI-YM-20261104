import YM.Integration.WilsonOriginalTwoFlatReflection
import YM.Integration.WilsonOriginalTwoFlatCompact
import YM.Integration.WilsonThermometerUnitFilingFlatTelescope

/-! Each finite Haar defect is evaluated at both older flat fields.
The rough reflected capital and the smaller freshly filed compact capital
apply to different intervals of one original experiment. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatTelescope
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells Real Marker
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j p)

def entrance {z K:ℕ}(Y:Cut C N p)(zK:z ≤ K)(kN:K ≤ N)(M:∀j:ℕ,(X j)→ℂ):ℝ:=
  ‖reading R (N:=N) (credit C N p 0 Y K kN) z zK-
    reading R (N:=N) (numerator R N p K (M K)) z zK‖

theorem interval {z c K:ℕ}(zc:z ≤ c)(ck:c ≤ K)(kn:K ≤ N)
    (M:∀j:ℕ,(X j)→ℂ)
    (paid:∀j,c ≤ j → j ≤ K → Integrable (numerator R N p j (M j)) (prior G _)):
    reading R (N:=N) (numerator R N p K (M K)) z (zc.trans ck)-
      reading R (N:=N) (numerator R N p c (M c)) z zc =
      ∑j∈Ico c K,feeAt R N p z M j:=by
  let f:=fun j=>if hj:z ≤ j then reading R (N:=N) (numerator R N p j (M j)) z hj else 0
  have changes:(∑j∈Ico c K,feeAt R N p z M j)=∑j∈Ico c K,(f (j+1)-f j):=by
    refine sum_congr rfl fun j hj=>?_
    obtain ⟨cj,jk⟩:=mem_Ico.mp hj
    have zj:=zc.trans cj
    simp only [f,feeAt,dif_pos zj,dif_pos (zj.trans (Nat.le_succ j))]
    exact edge R N p zj (jk.trans_le kn) M (paid j cj jk.le) (paid _ (cj.trans (Nat.le_succ j)) jk)
  rw [changes,sum_Ico_eq_sub _ ck]
  simp_rw [sum_range_sub]
  simp only [f,dif_pos (zc.trans ck),dif_pos zc]
  abel

private theorem defect {z c K:ℕ}(zc:z ≤ c)(ck:c ≤ K)(kn:K ≤ N)
    (Y:Cut C N p)(hc:Continuous Y)(M:∀j:ℕ,(X j)→ℂ)
    (paid:∀j,c ≤ j → j ≤ K → Integrable (numerator R N p j (M j)) (prior G _)):
    ‖reading R (N:=N) (credit C N p 0 Y c (ck.trans kn)) z zc-
      reading R (N:=N) (numerator R N p c (M c)) z zc‖ ≤
      entrance R Y (zc.trans ck) kn M+∑j∈Ico c K,‖feeAt R N p z M j‖:=by
  have same:reading R (N:=N) (credit C N p 0 Y c (ck.trans kn)) z zc=
      reading R (N:=N) (credit C N p 0 Y K kn) z (zc.trans ck):=by
    unfold reading
    rw [cutoff R (ck.trans kn) zc Y hc,cutoff R kn (zc.trans ck) Y hc]
  rw [same]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (reading R (N:=N) (numerator R N p K (M K)) z (zc.trans ck)) _).trans ?_
  rw [interval R zc ck kn M paid]
  exact add_le_add (le_refl _) (norm_sum_le (Ico c K) (fun j=>feeAt R N p z M j))

theorem original (simple:G.Simple){u v c K j:ℕ}(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(kn:K ≤ N)
    (cN:c<N)(jN:j ≤ N)(ou:Opened C 0 u p)(ov:Opened C 0 v p)
    (Y:Cut C N p)(hc:Continuous Y)(B:(C).label 0){a e rem:ℝ}
    (ret:WholeProductCapture.Retained C N c p 0 u R.makes ou (uv.trans vc) cN Y B a)
    (inside:Interior ((center (C).S p jN 0).chamber 0) (Y-(C).O N p B 0))
    (root:(center (C).S p jN 0).rootTest ((C).beta N p) (Y-(C).O N p B 0) ≤ e)
    (M:∀j:ℕ,(X j)→ℂ)(paid:∀j,c ≤ j → j ≤ K → Integrable (numerator R N p j (M j)) (prior G _))
    (stored:WilsonCenteredFiledAtoms.Store ((C).path.rep N p c) ((C).localSection 0)
      (C).params 0 (safety C c) rem (numerator R N p c (M c))):
    ‖(C).omega N p Y-reading R (N:=N) (credit C N p 0 Y c cN.le) v vc‖ ≤
      (e+a/gainChart (C).path c u)+
      (entrance R Y ((uv.trans vc).trans ck) kn M+∑j∈Ico c K,‖feeAt R N p u M j‖)+
      2*capital C c rem 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8)+
      (entrance R Y (vc.trans ck) kn M+∑j∈Ico c K,‖feeAt R N p v M j‖):=by
  let native:=(credit C N p 0 Y c cN.le)
  let word:=numerator R N p c (M c)
  have first:=WilsonOriginalTwoFlatReflection.original R simple (uv.trans vc) cN jN ou Y hc B ret inside root
  have fixed:=defect R (uv.trans vc) ck kn Y hc M paid
  have moving:=defect R vc ck kn Y hc M paid
  have transfer:=WilsonThermometerUnitFilingStops.two_stops R simple ou.post uv vc cN.le ou ov stored
  let top:=(C).omega N p Y
  let a₁:=reading R (N:=N) native u (uv.trans vc)
  let a₂:=reading R (N:=N) word u (uv.trans vc)
  let a₃:=reading R (N:=N) word v vc
  let a₄:=reading R (N:=N) native v vc
  have span:‖top-a₄‖ ≤ ((‖top-a₁‖+‖a₁-a₂‖)+‖a₂-a₃‖)+‖a₄-a₃‖:=by
    calc
      _ ≤ ‖top-a₃‖+‖a₄-a₃‖:=by simpa only [norm_sub_rev a₃ a₄] using norm_sub_le_norm_sub_add_norm_sub top a₃ a₄
      _ ≤ _:=by gcongr;exact (norm_sub_le_norm_sub_add_norm_sub top a₂ a₃).trans (add_le_add (norm_sub_le_norm_sub_add_norm_sub top a₁ a₂) (le_refl _))
  exact span.trans (add_le_add (add_le_add (add_le_add first fixed) transfer) moving)

end YM.Integration.WilsonOriginalTwoFlatTelescope
end
