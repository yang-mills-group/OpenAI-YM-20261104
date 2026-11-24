import YM.Integration.WilsonOriginalPublicTrialPhaseCapture
import YM.Integration.WilsonOriginalPublicTrialPhaseZero

/-! Keep each past scalar in the primal N-vacuum when the stable column advances. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseScalar
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open RG05Readout RG05Readout.Address
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}

def deposit (A:Rep G n)(X:Three G n)(z:ℂ): Three G n :=
  (X.1+z • (Complex.ofReal ∘ A.eval), fun U=>X.2.1 U+z, X.2.2)

theorem useful {A:Rep G n}{X:Three G n}{σ C Λ δ w:ℝ}(ok:A.Lawful σ C Λ δ w)
    (hx:Useful A X)(z:ℂ): Useful A (deposit A X z):=by
  refine ⟨hx.normK,?_,hx.integr.add ((((A.envelope ok).integrable _).ofReal).smul z)⟩
  ext U
  change ((A.eval U:ℂ)*(X.2.1 U+z)+_)=X.1 U+z*((A.eval U:ℝ):ℂ)
  rw [←hx.read]
  unfold coin deposit
  ring

variable (R:Run G){m N per:ℕ}
local notation "S" => R.family.path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per

set_option maxHeartbeats 650000 in
/-- A scalar shifts the ordinary log and the same true density on both sides.
The emitted forced owner, including its purchase and response, is preserved. -/
theorem original (live:m<N)(o:Site (R.family.side (m+1) per))(b:Site (R.family.side m per))
    (X:Three G (R.family.side (m+1) per))(Y:Three G (R.family.side m per))
    (bill:ℝ)(z:ℂ)(h:Ride (O) o b (R.doors N per m live) 1 X Y bill):
    Ride (O) o b (R.doors N per m live) 1 (deposit (P) X z) (deposit (Q) Y z) (bill+‖z‖):=by
  have hp:=(R.makes.wilson.represents N per (m+1) live).good
  have hq:=(R.makes.wilson.represents N per m live.le).good
  have up:=useful hp h.old z
  have dn:=useful hq h.tomorrow z
  refine ⟨up,dn,?_,?_⟩
  · obtain ⟨keys,finite,c,hc,ι,count,leaves,amount,answer,rec⟩:=h.pays
    refine ⟨keys,finite,c+z,(norm_add_le ..).trans (add_le_add hc le_rfl),ι,count,leaves,amount,answer,?_⟩
    have wider:=le_add_of_nonneg_right (a:=bill) (norm_nonneg z)
    exact ⟨rec.member,⟨rec.purchase.1,rec.purchase.2.1,rec.purchase.2.2.trans wider⟩,stackFee rec.cost wider,
      fun U=>by simpa only [deposit,add_sub_add_right_eq_sub] using rec.lyric U,rec.old,rec.grants⟩
  · have hi:Integrable (Complex.ofReal ∘ (P).eval) (prior G _):=(((P).envelope hp).integrable _).ofReal
    have vac:(O).push (P).beta (Complex.ofReal ∘ (P).eval)=Complex.ofReal ∘ (Q).eval:=by
      rw [MergeProof.Float.flash]
      exact congrArg (fun f:Config G (R.family.side m per)→ℝ=>Complex.ofReal ∘ f)
        (R.makes.wilson.steps N per m live).1.symm
    change Y.1+z • (Complex.ofReal ∘ (Q).eval)=1 • (O).push (P).beta (X.1+z • (Complex.ofReal ∘ (P).eval))
    rw [StepData.push_add ((S).levels.transition_mass ..) _ _ h.old.integr (hi.smul _),
      Address.preserves, vac,one_smul,h.exactStep,one_smul]
    rfl

end YM.Integration.WilsonOriginalPublicTrialPhaseScalar
end
