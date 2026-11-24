import YM.RG11Proof.Rigidity.Ice.Pledge

/-!
# Coherence of a color shift on all the top covectors
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd Prism
open scoped Classical BigOperators
variable {G : Gauge}{F : Frames G}{d:ℕ}
local notation "V"=>G.Color

def traceOut (A : TaylorTower G) : System (G:=G):= fun i j=> faceMap j (cp i) (A j)
def films (O : V →L[ℝ] V) (A : TaylorTower G) : TaylorTower G:= fun j=> faceMap j O (A j)
lemma films_self (A:TaylorTower G): films (.id ℝ V) A=A:=by funext j; apply Subtype.ext; funext a b; apply ContinuousMultilinearMap.ext; intro v; rfl
lemma reel_film (O P: V→L[ℝ] V)(A:TaylorTower G): films O (films P A)=films (O.comp P) A:=by
  funext j; apply Subtype.ext; funext a b; apply ContinuousMultilinearMap.ext; intro v; rfl

lemma trace_paint (A:TaylorTower G)(M:Mirror G) : Reads.paint (traceOut A) M= films (grid M).toContinuousLinearMap A:=by
  funext j; apply Subtype.ext; funext a b; apply ContinuousMultilinearMap.ext; intro v
  unfold Reads.paint traceOut films fill; simp_rw [face_eval]
  -- collect fin basis
  simp_rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,sum_apply,SetLike.val_smul,Pi.smul_apply,smul_apply, face_eval]
  ext1 k
  change (∑ x:G.ColorIndex,∑ s:G.ColorIndex, M (x,s) • (((↑(A j):TwoJet V j) a b v s) • unitColor G x)) k=_
  simp [unitPaint,mul_ite,grid,WithLp.ofLp_sum,Finset.sum_apply]

abbrev steers (O:Wheel G): V→L[ℝ] V:= O.toContinuousLinearEquiv

lemma gr_paint {b : Buffer F d}(h:Frigid b)(he:4≤d)(hG:G.Simple)(t:ℝ):
    ∃ O : Wheel G,∀ i : News F d,∀ Q : TaylorTower G,
      probe Q (writes F d i.v)=probe (films (steers O) Q) (Reads.top i.n (writes F d (drive b.val i.v t))) :=by
  obtain ⟨o,ho⟩:= theirs (Maxwell.Free.coreColor hG) (h.pledge he hG t) (gram_scoop h he hG t)
  refine ⟨o,fun i Q=> ?_⟩
  have H:=ho i (traceOut Q)
  unfold Performer.data at H
  have H': (↑(topSample (sources.slate i) i.n (traceOut Q) (board G)):ℂ)=(↑(topSample ((posed b t).slate i) i.n (traceOut Q) (roster o)):ℂ):= congrArg ((↑):ℝ→ℂ) H
  rw [← prints_out,← prints_out,← Reads.prints,← Reads.prints,trace_paint,trace_paint,
    show (grid (board G)).toContinuousLinearMap = ContinuousLinearMap.id ℝ V from ContinuousLinearMap.ext (fun x=>grid_board x),
    films_self] at H'
  have hQ:(grid (roster o)).toContinuousLinearMap=steers o:= ContinuousLinearMap.ext fun x=>grid_roster _ _
  rw [hQ, show canon (sources.slate i)=_ from (drawn _ i.base i.real).1,
    show canon ((posed b t).slate i)=writes F _ _ from (drawn (drive b.val i.v t) (directs b t _ i.price i.base) (drive_real b t _ i.real)).1,
    show Reads.top i.n (writes F d i.v)=_ from MvPolynomial.weightedHomogeneousComponent_eq_self i.gr] at H'
  exact H'

end YM.RG11.Rigidity.Ice
