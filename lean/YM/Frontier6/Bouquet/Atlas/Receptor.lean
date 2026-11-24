import YM.Frontier6.Bouquet.Audit.Freight

/-! At all pits of a parent's integration charge, including when memory far,
 book the portion still present at that cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier.Court
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}
variable {P:Ensemble}{i:P}(Z:Court i)
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (R: Air (S:=S) P I L Y)
set_option quotPrecheck false
local notation "Q"=> Z.split
variable {d:Slot→ℕ}{f g:Full (fiber P)}{A a B:ℝ}{j:ℕ}{M:Pod→ℝ}{x:I}
lemma byWind (hc: lodge P (R.lengths x) f B)(hp: tsupport g⊆tsupport f) : lodge P (R.lengths x) g B:=fun i=>Set.Subset.trans hp (hc i)
lemma recruits (ha:Fair f (R.region x).foot (R.region x).center)(hc:lodge P (R.lengths x) f B)(hx:Z.Contains (R.lengths x i) f)(hh: tsupport g ⊆ tsupport f)(he:Checks (fiber P) (paths P (R.lengths x)) g j A)(z:Margin P (Z.split))(hz:Z.Love R x z) :
    let y:Z.Volunteers R:=⟨(x,z),hz⟩
    let Y:=Z.newWorld R
    Fellow Z.split (Y.lengths y) (Y.region y) B (restrictS (plan_sub Z.legend.le) (insideCL loft_le z) g) j A:=by
    intro y Y; let U:= restrictS (plan_sub Z.legend.le) (insideCL loft_le z) g; change Fellow Z.split (R.lengths x ∘ assign Z.legend.le) (toAura R Z x z) B U j A; refine ⟨?_, relaxed _ _ _ (byWind R hc hh), ?_⟩
    · exact fun u hu q i hi=> Z.necklace (R.region x) (R.length_pos x _) ha hx (hh (restrict_support (plan_sub Z.legend.le) _ g hu)) q i hi
    exact Bouquet.Checks.bound_restrict (plan_sub Z.legend.le) he _ (paths_lesser Z.legend.le _) (paths_frame ..)
lemma loveless (h:R.Welkin M)(hc:Fellow P (R.lengths x) (R.region x) B f j A)(hx: Z.Contains (R.lengths x i) f)(T: Veins)(z:Margin P Z.split)(hv:¬Z.Love R x z) : slit T Z.legend.le z f=0:= Z.restrict_empty (A:=R) h (hc.fair.narrower (T.film_support _ _ _)) (fun y hy=> hx y (T.film_support P Z.split f hy)) hv -- arg order
lemma support_moves (hc:Fellow P (R.lengths x) (R.region x) B f j A)(T: Veins)(z:Margin P Z.split)(hz:B*R.lengths x i< ‖z‖): slit T Z.legend.le z f=0:=by
   ext1 y; let u:= forward (plan_sub Z.legend.le) (insideCL loft_le z) y; change T.film P Z.split f u=0; apply image_eq_zero_of_notMem_tsupport; exact fun hy=> (not_le.mpr hz) ((Z.legend.margin_rune u y z rfl).trans ((mem_closedBall_zero_iff.mp (hc.local_ i (T.film_support _ _ f hy)))))
abbrev offspring (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i))(s a:ℝ)(x:I)(f:Full (fiber P)) (z: Margin P Z.split):= Glued K (prepared K (common a) d v s) (common a) Z.legend.le (R.region x).center (R.sky x) f z
lemma uninhabited (v:(i:Slot)→S.Field (d i))(s a:ℝ)(z:Margin P Z.split)(hz:slit (common a) Z.legend.le z f=0) : offspring Z R K d v s a x f z=0:=by unfold offspring Glued; rw [hz]; exact select_zero ..
end YM.Frontier6.Bouquet.Atelier.Court
