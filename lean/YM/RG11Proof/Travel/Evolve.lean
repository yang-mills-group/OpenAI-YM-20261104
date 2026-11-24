import YM.RG11Proof.Travel.PDE
import YM.RG11Proof.Scale.Separating
import YM.RG11Proof.Formal.Orbit

/-! # Finite flow law on separated arrays from triangular CS + detection -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Travel
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Scale
open scoped BigOperators Classical Topology
variable {J P:Type*}[Fintype J]{arity:P→ℕ}
local notation "ps"=>PowerSeries ℝ

def step (w:J→ℕ)(t:ℝ→Keeper arity)(s:ℝ)(A:ArrayAt J ℝ arity): ArrayAt J ℝ arity:=fun v=>PowerSeries.C (Real.exp (-bulk w v*s))*A ((t s).move v)

 theorem acts_bulk (w:J→ℕ)(t:ℝ→Keeper arity)(s:ℝ)(A:ArrayAt J ℝ arity)(p:Change ℝ J)(hp:Anchored p.g)(hz:graded w p.Z)(v):
    step w t s (p.act A) v=p.act (step w t s A) v:=by
   rw [step,Keeper.move_act,Change.act,Change.act]; unfold YM.PertExtension.Position.insert; rw [Finset.mul_sum]
   let f:ps→ₐ[ℝ] ps:=substAlgHom (R:=ℝ) hp.permits
   apply Finset.sum_congr rfl; intro u _; dsimp only [step,Function.comp_apply]; simp_rw [←coe_substAlgHom (R:=ℝ) hp.permits,map_mul,show ∀ x:ℝ,substAlgHom (R:=ℝ) hp.permits (C x) = C x from (substAlgHom (R:=ℝ) hp.permits).commutes]
   by_cases h:∀ i,w (v.2 i)=w (u i)
   · have he:bulk w v=bulk w (⟨v.1,u⟩:Mark J arity):=by unfold bulk; apply Finset.sum_congr rfl; intro i _; rw [h i]
     rw [he,mul_assoc]
   obtain ⟨i,hi⟩:=not_forall.mp h
   rw [Finset.prod_eq_zero (Finset.mem_univ i) (@hz (v.2 i) (u i) hi)]; simp

 theorem demands {N}(w:J→ℕ)(t:ℝ→Keeper arity)(s:ℝ){A B:ArrayAt J ℝ arity}(h:∀ v,Through N (A v) (B v))(v):
    Through N (step w t s A v) (step w t s B v):=(Through.refl _).mul (h _)

-- derivative through N. Call β b linear and commute engineering scaling. hZ graded needed.
 theorem on_shape (w:J→ℕ)(t:ℝ→Keeper arity){A:ArrayAt J ℝ arity}{N}
    (E:Keeper arity)(hr:Respiration t E A N)(K:Static J)(hm:graded w K.b)(he:Stem N E w A K.β K.b)(s:ℝ)(v:Mark J arity):
    Speed (fun u=>step w t u A v) s (call K.β K.b (step w t s A) v) N:=by
   let V:=bulk w v
   let B:=PowerSeries.C (Real.exp (-V*s))
   have h (i:Fin (arity v.1))(j:J)(h:w (v.2 i)=w j): bulk w (⟨v.1,Function.update v.2 i j⟩:Mark J arity)=V:=by
      unfold V bulk; apply Finset.sum_congr rfl; intro k _; by_cases he:k=i
      · subst k; simp [h]
      simp [Function.update_of_ne he]
   have hw : orbit (step w t s A) v K.b=B*orbit A ((t s).move v) K.b:=by
      rw [Keeper.move_orbit]; unfold orbit; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      by_cases h':w (v.2 i)=w j
      · rw [step,h i j h']; exact mul_left_comm ..
      rw [hm h']; simp
   have hy : call K.β K.b (step w t s A) v=B*call K.β K.b A ((t s).move v):=by
      rw [call,hw]; change K.β * derivative ℝ (C _ * A _) - _ = _*(_ -_)
      rw [Derivation.leibniz,derivative_C,smul_zero,add_zero]; change K.β * (B*_) - _ = _*(_-_); ring
   intro k hk
   simp_rw [step,coeff_C_mul]
   change HasDerivAt (fun t':ℝ=>Real.exp (-V*t')* coeff k (A ((t t').move v))) _ s
   have hb:HasDerivAt (fun t':ℝ=> Real.exp (-V*t')) ((-V)*Real.exp (-V*s)) s:=by simpa only [mul_comm,one_mul] using (((hasDerivAt_id' s).const_mul (-V)).exp)
   have hq:=hb.mul (hr k hk v s)
   convert! hq using 1
   rw [show call _ _ _ _=_ from hy]; unfold B; rw [coeff_C_mul, ←he _ k hk,euler,map_sub,coeff_C_mul,bulk_cast]; unfold V; ring

namespace Static
def opposite (K:Static J):Static J:= {
   K with
   b:= -K.b
   still:= by
     ext i j; change coeff 0 (-(K.b i j))=0; rw [map_neg,←piece_apply (A:=K.b),K.still]; simp }

-- Use s0=identity and apply solves. No requirement on K.b legal for covariance itself, just graded. Need legal V for unique scaling as frame/coupling change.
 theorem against (K:Static J){w:J→ℕ}{t:ℝ→Keeper arity}(ht:t 0=Keeper.id arity){A:ArrayAt J ℝ arity}{N}
    (E:Keeper arity)(hr:Respiration t E A N)(hm:graded w K.b)(he:Stem N E w A K.β K.b)(s:ℝ)(v:Mark J arity):
    Through N (step w t s A v) ((K.opposite.changeBy s).act A v):=by
   apply uniqueness (K:=K) (fun s=>step w t s A) (fun s=>(K.opposite.changeBy s).act A)
   · intro v; rw [step,ht,Keeper.move_id,strikes,Change.act_one]; simp only [mul_zero,Real.exp_zero,map_one,one_mul]; exact Through.refl _
   · exact on_shape w t E hr K (fun hh=> hm hh) he
   intro s v
   have hv:= K.opposite.solves A N s v; change Speed _ _ (call K.β (-(-K.b)) _ _) _ at hv; rwa [neg_neg] at hv
end Static

-- Scale changes interrelated at finite s, not just β & gamma.
 theorem together (w:J→ℕ){t:ℝ→Keeper arity}(s:ℝ) (A B:ArrayAt J ℝ arity)(p x y:Change ℝ J){L:Constraints ℝ J}(hp:Change.Good L p)(hx:Change.Good L x)(hy:Change.Good L y)
    {N}(hm:graded w p.Z)(h:∀ v,Through N (p.act A v) (B v))(hu:Sees L A)
    (he:∀ v,Through N (step w t s A v) (x.act A v))
    (ht:∀ v,Through N (step w t s B v) (y.act B v)):
   Change.EquivJet (p.compose x) (y.compose p) N:=by
   have hq(v:Mark J arity): Through N ((p.compose x).act A v) ((y.compose p).act A v):=by
      simp_rw [←Change.act_act _ _ hp.ruler.base hx.ruler.base, ←Change.act_act _ _ hy.ruler.base hp.ruler.base]
      have ha : Through N (p.act (x.act A) v) (p.act (step w t s A) v):=Change.EquivJet.refl.act hp.ruler.base (fun i=>(he _).symm)
      rw [←acts_bulk w _ s _ p hp.ruler.base (fun h=>hm h)] at ha
      exact ha.trans ((demands w t s h v).trans ((ht v).trans (Change.EquivJet.refl.act hy.ruler.base (fun i=>(h _).symm))))
   have hg:=hp.compose hx; have hg':=hy.compose hp
   exact (Formal.identification (Detector.ofSees hu) ⟨hg.ruler.base,hg.field⟩ (fun _=>(hq _).symm)).trans (Formal.identification (Detector.ofSees hu) (B:=(y.compose p).act A) ⟨hg'.ruler.base,hg'.field⟩ (fun _=>Through.refl _)).symm
end YM.RG11.Travel
