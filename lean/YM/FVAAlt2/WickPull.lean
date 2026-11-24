import YM.MS.Swirl.Plane
import YM.FVAAlt2.Pull

/-!
# covariance under finite linear field maps; normalized `Endμ`

Important factor: in MS native convention K is half the pairing covariance.
This is a congruence `L.transpose*K*L`, never a Hermitian pullback.
We need no nonsingularity on either field family. We prove naturality including
moments and denominators (not just individual cumulants).
-/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.FVAAlt2
open MS MS.Koszul MS.Plane MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl
open Finset MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Engine MS.Puff.Mom MS.Cylinder
variable {I J : Type}[Fintype I][Fintype J]

def pullCov (K: Matrix J J ℂ)(L: Matrix J I ℂ) := L.transpose * K * L

lemma pull_frame (K : Matrix J J ℂ) (L : Matrix J I ℂ) (U : Raw I ℂ):
    Orbit.Cog.frame K (pull L U)=pull L (Orbit.Cog.frame (pullCov K L) U):= by
  rw [fpΩ,fpΩ]
  unfold pullCov; simp only [diffPair_apply,pull_D,map_smul,map_sum,smul_sum, Finset.sum_smul, smul_smul, Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  let g : J × J → I × I → Raw J ℂ := fun w v =>
    (L w.1 v.1 * K w.1 w.2 * L w.2 v.2) • pull L (D v.2 (D v.1 U))
  have he: (∑ i:J,∑ j:J,∑ x:I,∑ y:I,g (i,j) (x,y))=∑ x:I,∑ y:I,∑ i:J,∑ j:J,g (i,j) (x,y) := by
    have h : (∑ w:J×J,∑ v:I×I,g w v) = ∑ v:I×I,∑ w:J×J,g w v:= Finset.sum_comm
    simpa only [Fintype.sum_prod_type] using h
  refine Eq.trans (Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> ?_) (he.trans (sum_congr rfl fun x _=> sum_congr rfl fun y _=> Finset.sum_comm))
  unfold g; dsimp only; rw [show L i x * K i j * L j y= K i j*(L i x * L j y) from by ring]

lemma pull_tep (K : Matrix J J ℂ) (L : Matrix J I ℂ) (n : ℕ) (U : Raw I ℂ):
    tep K n (pull L U)=pull L (tep (pullCov K L) n U):= by
  induction n with
  | zero=> rw [rise,rise]; rfl
  | succ n ih=> rw [teen,teen,ih,pull_frame,map_smul]
lemma pull_effect (K : Matrix J J ℂ) (L : Matrix J I ℂ) (n : ℕ) (U : Raw I ℂ):
    effect K n (pull L U)=pull L (effect (pullCov K L) n U):= by
  unfold effect; simp_rw [LinearMap.sum_apply,map_sum,pull_tep]

lemma pull_View (K : Matrix J J ℂ) (L : Matrix J I ℂ) {F : Raw I ℂ}
    (h : F ∈ Mini I) : View K (pull L F)=View (pullCov K L) F:= by
  obtain ⟨n,h⟩:=h; change Shot K _ [] = Shot (pullCov K L) F []
  rw [dawn K (pull_limit L h),dawn _ h, pull_effect]; rfl

variable {L : Matrix J I ℂ}{p:Sector I}{q:Sector J}
lemma pull_Tether (hp:Tie p q L): Tether (pull L) (actor p) (actor q) :=
  ⟨pull_coin L 1, fun f g=> pull_product hp f g⟩

abbrev pullSeries (L: Matrix J I ℂ): (SpecB I)→ₗ[ℂ](SpecB J) := pointL ℕ (pull L)

lemma exp_pull (hp:Tie p q L)(U:SpecB I):
    pullSeries L (exp0 p U)=exp0 q (pullSeries L U):= funext fun i=> (pull_Tether hp).figure useN U i
lemma pull_core (hp:Tie p q L)(v u:SpecB I):
    pullSeries L ((PermV p).core v u)=(PermV q).core (pullSeries L v) (pullSeries L u):=
  ((pull_Tether hp).Extrapolation useN).craft _ _
lemma pull_font {W:Type}[LinearOrder W](hp:Tie p q L)(U:Mate I W)(s:Finset W) :
    Font q (fun x=>pullSeries L (U x)) s = pullSeries L (Font p U s):=
  (((pull_Tether hp).Extrapolation useN).figure (marked W) U s).symm
lemma pull_fee (hp:Tie p q L){F:Raw I ℂ}(H:F∈ FeeP p): pull L F∈ FeeP q:=by
  obtain ⟨he,n,hx⟩:=fee_spec H
  exact ⟨pull_symm hp he,minH (pull_limit L hx)⟩
lemma pullΓ (hp:Tie p q L){F:SpecB I}(h:Γ F p): Γ (pullSeries L F) q := fun i _=>pull_fee hp (h i (Set.mem_univ _))
lemma wick_pull (_hp:Tie p q L) (K: Matrix J J ℂ) {F:SpecB I}(H: Γ F p):
    ℶV K (pullSeries L F)=ℶV (pullCov K L) F:= funext fun i=> pull_View K L (fee_spec (H i (Set.mem_univ _))).2

lemma numerator_pull (hp:Tie p q L) (K: Matrix J J ℂ){U F:SpecB I}(h:Γ U p)(he:Γ F p):
    ℶV K ((PermV q).core (exp0 q (pullSeries L U)) (pullSeries L F))=
      ℶV (pullCov K L) ((PermV p).core (exp0 p U) F):= by
  rw [← exp_pull hp,← pull_core hp, wick_pull hp K (ΤΓ_pair (expΓ h) he)]
lemma end_pull (hp:Tie p q L) (K: Matrix J J ℂ) {U F:SpecB I}(h:Γ U p)(he:Γ F p){W: ℕ→ℂ}:
    Endμ K q (pullSeries L U) (pullSeries L F) W ↔ Endμ (pullCov K L) p U F W:= by
  unfold Endμ; rw [numerator_pull hp K h he,← exp_pull hp,wick_pull hp K (expΓ h)]
end YM.FVAAlt2
