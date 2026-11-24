import YM.Integration.WilsonOriginalCensusAngularFace

/-! A fresh printed roster has a fixed physical rank allowance. Both the new group
words and the rows after the genuine measured restamp retain their original wages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPhysicalLoad
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open scoped BigOperators

variable {V:Type} [Fintype V] [DecidableEq V] {C:Census V}

def rank (d:Bool→V→ℕ):ℕ:=max (∑v,d false v) (∑v,d true v)

def head (d:Bool→V→ℕ)(s:C.Mode):ℕ:=max (Launch.index C (d false) s) (Launch.index C (d true) s)+1

def delay (d:Bool→V→ℕ)(s:C.Mode)(a:Bool):ℕ:=head d s-(Launch.index C (d a) s+1)

theorem total (d:Bool→V→ℕ)(a:Bool)(s:C.Mode):Launch.index C (d a) s ≤ rank d:=by
  have k:(∑v∈s.val,d a v) ≤ ∑v,d a v:=sum_le_sum_of_subset_of_nonneg (f:=d a) (subset_univ _)
    (fun _ _ _=>Nat.zero_le _)
  exact k.trans (by cases a <;> simp only [rank,le_max_iff,le_refl,true_or,or_true])

theorem cost (d:Bool→V→ℕ)(s:C.Mode):head d s ≤ rank d+1:=
  Nat.succ_le_succ (max_le (total d false s) (total d true s))

omit [Fintype V] in
theorem cleared (d:Bool→V→ℕ)(s:C.Mode)(a:Bool):
    head d s+0=delay d s a+(Launch.index C (d a) s+1):=by
  have le:Launch.index C (d a) s+1≤head d s:=by
    apply Nat.succ_le_succ
    cases a
    · exact le_max_left .. 
    · exact le_max_right ..
  unfold delay
  omega

variable {G:Gauge}{n:Side}{I X:Bool→Type}{P:Bool→Passport n V}
  {M:(a:Bool)→I a→Row (P a) C G (X a)}
  {w:Bool→V→ℝ}{d:Bool→V→ℕ}{σ b:Bool→ℝ}{p t h:Bool→ℕ}

theorem original (old:∀a,Armada (M a) (w a) (d a) (σ a) (b a) (p a) (t a) (h a)):
    ∀a,Armada (M a) (w a) (d a) (σ a) (b a) (p a) (Fintype.card V) (rank d):=by
  intro a
  refine ⟨⟨fun s=>Finset.card_le_univ s.val,total d a⟩,(old a).positive,(old a).suggests,
    (old a).purchases,(old a).honor⟩

end YM.Integration.WilsonOriginalCensusPhysicalLoad
end
