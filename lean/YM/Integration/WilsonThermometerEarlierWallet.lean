import YM.Integration.WilsonThermometerUnitFilingRawSum

/-! Adding signed true inputs on the original held-identity readings at all earlier dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerEarlierWallet
open Function Filter Finset MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato RG16 WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per i u t:ℕ}
local notation "X" => Config G (R.family.side t per)
local notation "read" => reading R (N:=N)

def Admitted (it:i≤t)(f:X→ℂ)(C:ℝ):Prop:=
  Integrable f (prior G _) ∧ ∀ (j : ℕ), u ≤ j → ∀ (ji : j ≤ i), ‖read f j (ji.trans it)‖ ≤ C

theorem signed (f g:X→ℂ)(hf:Integrable f (prior G _))(hg:Integrable g (prior G _))
    (j:ℕ)(jt:j≤t):read (f-g) j jt=read f j jt-read g j jt:=by
  have as:f-g=f+(-1:ℂ) • g:=by funext U;simp [sub_eq_add_neg]
  rw [as,WilsonThermometerUnitFilingRaw.add R f _ hf (hg.smul (-1:ℂ)) jt,
    WilsonThermometerUnitFilingRawSum.scaled R _ g hg jt,neg_one_mul,sub_eq_add_neg]

theorem minus {it:i≤t}{f g:X→ℂ}{A B:ℝ}
    (paid:Admitted (u:=u) (N:=N) R it f A)(peer:Admitted (u:=u) (N:=N) R it g B):
    Admitted (u:=u) (N:=N) R it (f-g) (A+B):=by
  refine ⟨paid.1.sub peer.1,?_⟩
  intro j uj ji
  rw [signed R _ _ paid.1 peer.1]
  exact (norm_sub_le ..).trans (add_le_add (paid.2 j uj ji) (peer.2 j uj ji))

theorem plus {it:i≤t}{f g:X→ℂ}{A B:ℝ}
    (paid:Admitted (u:=u) (N:=N) R it f A)(peer:Admitted (u:=u) (N:=N) R it g B):
    Admitted (u:=u) (N:=N) R it (f+g) (A+B):=by
  refine ⟨paid.1.add peer.1,?_⟩
  intro j uj ji
  rw [WilsonThermometerUnitFilingRaw.add R _ _ paid.1 peer.1]
  exact (norm_add_le ..).trans (add_le_add (paid.2 j uj ji) (peer.2 j uj ji))

theorem three {it:i≤t}{f:Fin 3→X→ℂ}{A:ℝ}
    (paid:∀v,Admitted (u:=u) (N:=N) R it (f v) A):
    Admitted (u:=u) (N:=N) R it (∑v,f v) (3*A):=by
  rw [Fin.sum_univ_three]
  convert plus R (plus R (paid 0) (paid 1)) (paid 2) using 1;ring

end YM.Integration.WilsonThermometerEarlierWallet
