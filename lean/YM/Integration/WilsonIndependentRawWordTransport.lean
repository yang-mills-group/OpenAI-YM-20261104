import YM.RegulatorIR.Tape.Scoria

/-! A full submitted invariant word uses one opening rooted expense through
the Wilson cover recursion, including its ordinary scalar feeds. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentRawWordTransport
open RegulatorIR RegulatorIR.Budget RegulatorIR.Uniform RegulatorIR.Ledger
open RegulatorIR.Ledger.Sky RegulatorIR.Taping RegulatorIR.Halo
open scoped ENNReal NNReal BigOperators Classical

variable {W:Type}{M:W→ℕ}{X Y:Page M→Type}{S:Sky X Y}{T:S.Accounts}
    {p m u k:ℕ}{L:Meter W}{c:Flap M→ℝ≥0∞}{x:W→Room}
    (Z:T.Report m){wage:W→ℝ≥0∞}

def Opening : Prop :=
  ∀ i, i≤p → ∀ r, Claim L (fun w=>S.coverQ x u (Page.opening M w)) wage
    (fun w=>Z.main (Page.opening M w) i r)

variable (P:S.Primitive L p k)(N:S.Supplies T L p k)
    (small:S.Lead u c)(h:u≤k)
    (basis:Opening (p:=p) (x:=x) (u:=u) (L:=L) Z (wage:=wage))
    (finite:∀ w,wage w≠⊤)
    (ward:∀ i e,e≤p→(S.sight i).Way (Z.main i.prev) e)

include small in
private theorem currency : S.Softness u L c 1 1 :=
  ⟨small,fun _=>one_ne_zero,fun _=>ENNReal.one_ne_top,
    fun f=>by simpa only [pow_one,Pi.one_apply,mul_one] using small.cap f,
    by simpa only [Pi.one_apply,inv_one,mul_one] using! Poly.oneQ (flapL M L),
    fun _=>le_rfl⟩

include P basis finite ward in
private theorem filed : S.Imprints T Z.main u p m x 1 wage 1 L where
  starts i hi r _ := by
    simpa only [ticket,Pi.one_apply,inv_one,mul_one] using! basis i hi r
  force i _ r := by
    have same (f:Flap M) : Z.main f.next i r-S.reportOut T Z.main m f i r=0 := by
      unfold reportOut
      rw [←Z.step_m f,sub_self]
    simp_rw [same]
    exact Claim.zeroQ
  consent := ward
  rank := fun a e _=>Z.cap_b P.grade a e
  sanctity := by intro a i j _ hj hc; omega
  compact := finite

include P N small h basis finite ward
/-- Paying the whole rooted word at its actual opening controls every
later cover coefficient of that same word. Rank zero includes its deposits. -/
theorem original {e r:ℕ} (he:e≤p) :
    Claim (coverL M L) (S.coverQ x u) (fun w=>wage w.bindW)
      (fun w=>Z.main w e r) := by
  let I:=filed Z P basis finite ward
  let C:=currency small (L:=L)
  have ht : ticket (1:Page M→ℝ≥0∞) wage=(fun w=>wage w.bindW) := by
    funext w; simp [ticket]
  cases r with
  | succ r =>
    rw [←ht]
    exact S.glides T Z.main P N C I h e he (r+1) (Nat.succ_pos r)
  | zero =>
    have fed := S.till T Z.main P N C I h he
    have top := Carry.us (basis e he 0) (Page.bindW (M:=M))
    rw [ht] at fed
    change Carry (coverL M L) (fun w=>wage w.bindW) _ at fed
    apply Carry.mono (Carry.add fed top)
    intro w
    dsimp only
    simp only [quotaNote]
    simpa only [sub_add_cancel] using enorm_add_le
      (note (Z.main w e 0)-note (Z.main (Page.opening M w.bindW) e 0))
      (note (Z.main (Page.opening M w.bindW) e 0))

theorem early (atRef:Choice M) :
    S.Preserved T Z wage 0 p atRef x u L := by
  intro i hi r
  simp only [pow_zero,inv_one,ENNReal.ofReal_one,one_mul]
  exact (Carry.us (original Z P N small h basis finite ward (r:=r) hi) atRef.before.page)

end YM.Integration.WilsonIndependentRawWordTransport
