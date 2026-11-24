import YM.Integration.WilsonOriginalTwoFlatIRHeard

/-! The signed face on the original Wilson law is the sum of its six
dated contributions. The same complete captured numerator is used at both
older flats. The terminal target can contain an independent old scalar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseIdentity
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels
open Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatTelescope WilsonOriginalTwoFlatGridScaling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per K c u v:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)
local notation "read" j:max M:max b:max h:max =>
  reading R (N:=N) (numerator R N per j M) b h

def entry (uk:u≤K)(kn:K≤N)(Y:Cut C N per)(M:∀j:ℕ,(X j)→ℂ):ℂ:=
  reading R (N:=N) (credit C N per 0 Y K kn) u uk-read K (M K) u uk

def cross (uc:u≤c)(vc:v≤c)(M:∀j:ℕ,(X j)→ℂ):ℂ:=
  read c (M c) u uc-read c (M c) v vc

theorem figure (uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (Y:Cut C N per)(cont:Continuous Y)(M:∀j:ℕ,(X j)→ℂ)
    (paid:∀j,min u v≤j→j≤K→Integrable (numerator R N per j (M j)) (prior G _))(Q:ℂ):
    (C).omega N per Y-Q =
      gap R N per u ((uc.trans ck).trans kn) Y+entry R (uc.trans ck) kn Y M+
      (∑j∈Ico c K,feeAt R N per u M j)+cross R (N:=N) uc vc M+
      (∑j∈Ico v c,feeAt R N per v M j)+(M v 1-Q):=by
  have same:reading R (N:=N) (credit C N per 0 Y u ((uc.trans ck).trans kn)) u le_rfl=
      reading R (N:=N) (credit C N per 0 Y K kn) u (uc.trans ck):=by
    dsimp only [reading]
    rw [cutoff R _ le_rfl Y cont,cutoff R kn (uc.trans ck) Y cont]
  have top:=interval R uc ck kn M (fun j cj jk=>paid j (((min_le_left _ _).trans uc).trans cj) jk)
  have low:=interval R le_rfl vc (ck.trans kn) M (fun j vj jc=>paid j ((min_le_right _ _).trans vj) (jc.trans ck))
  have bot:read v (M v) v le_rfl=M v 1:=by
    have normed:read v (M v) v le_rfl=actualTransport C (N:=N) (M v) le_rfl 1:=
      WilsonThermometerUnitFilingPosterior.weighted R (N:=N) (M v) le_rfl
    rw [normed,actualTransport_base C R.makes ((vc.trans ck).trans kn)]
  rw [←top,←low,bot,gap,same,entry,cross]
  abel

theorem price (uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (Y:Cut C N per)(cont:Continuous Y)(M:∀j:ℕ,(X j)→ℂ)
    (paid:∀j,min u v≤j→j≤K→Integrable (numerator R N per j (M j)) (prior G _))(Q:ℂ)
    {a b h:ℝ}(phase:‖gap R N per u ((uc.trans ck).trans kn) Y‖ ≤ a)
    (joined:‖entry R (uc.trans ck) kn Y M‖ ≤ b)(charged:‖cross R (N:=N) uc vc M‖ ≤ h):
    ‖(C).omega N per Y-Q‖ ≤ a+b+(∑j∈Ico c K,‖feeAt R N per u M j‖)+h+
      (∑j∈Ico v c,‖feeAt R N per v M j‖)+‖M v 1-Q‖:=
  (norm_sub_le_norm_sub_add_norm_sub _ (M v 1) _).trans (add_le_add
    (WilsonOriginalTwoFlatIRHeard.terminal R uc vc ck kn Y cont M paid phase joined charged) le_rfl)

end YM.Integration.WilsonOriginalTwoFlatRoseIdentity
