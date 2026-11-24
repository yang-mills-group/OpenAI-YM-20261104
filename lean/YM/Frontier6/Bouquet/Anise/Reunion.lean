import YM.Frontier6.Bouquet.Anise.Mail

/-! Moving one Elevator through the other slots. Every Cartesian slicing
 of a Full test (including its normal derivatives) keeps this equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q][FiniteDimensional ℝ R]
namespace Tandem
variable (h:Tandem P Q R)
include h
lemma inside_loft : Q≤ Loft R P := le_inf h.orth h.rgt
lemma detached (f g:Full R)(hh: ∀ i:Q, restrictS h.lft (insideCL h.rgt i) f= restrictS h.lft (insideCL h.rgt i) g): f=g:=by
    ext1 i; obtain ⟨⟨x,y⟩,hy⟩:= h.decoration.surjective i; change h.together (x,y)=i at hy; rw [h.knows_right] at hy; rw [← hy]; exact DFunLike.congr_fun (hh y) x
def sampleL (x:P) : Full R→ₗ[ℂ] Full Q:= restrictS h.rgt (insideCL h.lft x)
def sampleR (x:Q) : Full R→ₗ[ℂ] Full P:= restrictS h.lft (insideCL h.rgt x)
lemma sample_left (x:P)(y:Q)(f:Full R):sampleL h x f y=f (h.together (x,y)):=by unfold sampleL; rw [restrict_at,h.knows_left]
lemma sample_right (x:P)(y:Q)(f:Full R):sampleR h y f x=f (h.together (x,y)):=by unfold sampleR; rw [restrict_at,h.knows_right]
abbrev Essay (P:Place) := Full P →ₗ[ℂ] Full P
lemma sample_move (F:Essay P)(T:Essay R)(he:Elevator h.lft F T)(f:Full R)(y:Q): sampleR h y (T f) = F (sampleR h y f):=he.acts f (insideCL h.inside_loft y)
lemma plane_motion {s:Multiset Room}(hs:∀ i∈s,i∈ Q)(F:Essay P)(T:Essay R)(hh:Elevator h.lft F T)(f:Full R): train R s (T f)=T (train R s f):= Mobile.train_paths T s hh.moves (fun i hi=> h.inside_loft (hs i hi)) _
lemma stationary {g:Q→ℂ}(hg:Smooth g)(x:Q)(f:Full R): sampleR h x (paneM g hg f)=(g x) • sampleR h x f:=by
    ext1 y; rw [sample_right h, h.canonical]; unfold paneM; rw [screened,Function.comp_apply,map_add,h.symm.of_left,h.symm.of_right,zero_add,smul_apply,sample_right h,h.canonical]; rfl
lemma wed {g:Q→ℂ}(hg:Smooth g)(F:Essay P)(T:Essay R)(he: Elevator h.lft F T)(f:Full R): paneM g hg (T f)= T (paneM g hg f):=by apply h.detached; intro i; change sampleR h i _=sampleR h i _; rw [h.sample_move F T he,h.stationary,h.stationary,h.sample_move F T he,map_smul]
lemma stage_synced {u:P→ℂ}(hg:Smooth u)(z:Q)(f:Full R): sampleR h z (paneM u hg f)= screen u hg (sampleR h z f):= h.sample_move _ _ (Elevator.panes h.lft u hg) _ _
end Tandem
end YM.Frontier6.Bouquet
