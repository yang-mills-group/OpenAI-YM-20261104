import YM.Integration.WilsonNeutralBilinearRopes
import YM.Integration.WilsonNeutralNominatedFiniteTable

/-! Identify the two native field alphabets at their actual cutoff.  The
dictionary preserves each derivative multi-index.  Its plain letters therefore
carry the same measured numerical coefficient in both filed programs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralCutoffAlphabet
open FormalBulk08 Pose Dawn Chapel PowerSeries Lattice Labels Laurent RG Wilson
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonNeutralCopiedProgram WilsonNeutralCopiedField
open scoped BigOperators Classical

private def bag (a:Axis→ℕ):Multiset Axis:=∑ i,Multiset.replicate (a i) i

private lemma counted (a:Axis→ℕ)(i:Axis):(bag a).count i=a i:=by
  have parts (s:Finset Axis):(∑ v∈s,Multiset.replicate (a v) v).count i=
      ∑ v∈s,(Multiset.replicate (a v) v).count i:=by
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => simp [hx,ih]
  rw [bag,parts,Finset.sum_eq_single i]
  · simp
  · intro v _ ne; simp [Multiset.count_replicate,ne]
  · simp

private lemma number (a:Axis→ℕ):(bag a).card=Chapel.upper a:=by
  simp [bag,Chapel.upper,Multiset.card_sum]

private lemma assembled (s:Multiset Axis):bag (fun i=>s.count i)=s:=by
  ext i;exact counted _ i

def spiral (d:ℕ):Dawn.Spring d ≃ Embroider.Spiral d where
  toFun v:=⟨bag v.val,(number v.val).le.trans ((Dawn.paper_is _).mp v.prop)⟩
  invFun z:=⟨fun i=>z.val.count i,(Dawn.paper_is _).mpr (by rw [←number,assembled];exact z.prop)⟩
  left_inv v:=Subtype.ext (funext (counted v.val))
  right_inv z:=Subtype.ext (assembled z.val)

def filed {G:Gauge}{d:ℕ}(F:Frame G d):Pose.Letter F≃Alma F where
  toFun v:=⟨(mint F v,spiral d (pet F v)),by
    change (F.grades (mint F v)).1+(bag (pet F v).val).card≤d
    rw [number]
    exact (Finset.mem_filter.mp v.prop).2⟩
  invFun v:=⟨(v.val.1,(spiral d).symm v.val.2),Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by
      change (F.grades v.val.1).1+Chapel.upper (fun i=>v.val.2.val.count i) ≤d
      rw [←number,assembled];exact v.prop⟩⟩
  left_inv v:=Subtype.ext (Prod.ext rfl ((spiral d).symm_apply_apply _))
  right_inv v:=Subtype.ext (Prod.ext rfl ((spiral d).apply_symm_apply _))

theorem letters {G:Gauge}{d:ℕ}(F:Frame G d)(v:Pose.Letter F):
    sheet F (filed F v)=mint F v ∧
      (∀i,((filed F v).val.2.val).count i=(pet F v).val i) ∧
      Embroider.rankS (filed F v).val.2=Chapel.upper (pet F v).val:=by
  exact ⟨rfl,counted _,number _⟩

theorem point_eq {G:Gauge}(F:Frame G 4)(j:F.Index):
    filed F (WilsonNeutralBilinearLetters.plain F j)=point F j:=by
  apply Subtype.ext;apply Prod.ext rfl;apply Subtype.ext;apply Multiset.ext.mpr
  intro i;change (bag 0).count i=(0:Multiset Axis).count i;rw [counted];simp

end YM.Integration.WilsonNeutralCutoffAlphabet
end

