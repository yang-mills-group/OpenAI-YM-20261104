import YM.AlbaMS.Super.Radius

/-!
Rotation commutator (test only vars). Shift adjustment from charge.
In particular not assuming tilt under finite-chart based ghosts. Later
modules use on *bulk* large periodic calculations. Signs align with directed
nonminimal maps too, if represented within the grading rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function IsNilpotent
open scoped BigOperators Classical
variable {ι R : Type*} [CommRing R] {ρ:ι→Bool} {p : Bool}
variable {F G H : Coil ρ R} {k g : ι→ι→R} {s : Finset ι} {m n : ℕ} {i j : ι}
variable {U W : Module.End R (Coil ρ R)}

def Rotor (s : Finset ι)(U : Module.End R (Coil ρ R)):Prop:= ∃ v, U=tom s v ∧ ∀ i, Cap (v i) 1
namespace Rotor
lemma tethered (h:Graded ρ p k)(H:Cap F 2): Rotor s (tether p k s F) := ⟨_,LinearMap.ext fun _=> from_vectors p h, fun i=> cross_cap (m:=0) h H (var_cap (R:=R) i)⟩
lemma catches (u:Rotor s U)(h:Graded ρ false k): Twin s (touch k s*U-U*touch k s):=by
  obtain ⟨v,rfl,HV⟩:=u
  let L (i j : ι) := cross false k s (v i) (varC R ρ j); let g i j:=L i j []
  have hm i j: L i j= put ρ (g i j):= (cross_cap (n:=0) (m:=0) h (HV i) (var_cap j)).eroded
  have he {i:ι}(G : Coil ρ R): cross false k s (v i) G= ∑ j ∈ s,g i j • (D j G):=by
    rw [← from_tether, from_vectors false h, tom_apply]; apply Finset.sum_congr rfl; intro j _; change L i j*_=_; rw [hm,put_smul_left]
  refine ⟨g,LinearMap.ext fun i=>?_⟩; rw [LinearMap.sub_apply, Module.End.mul_apply,Module.End.mul_apply,tom_apply,tom_apply,map_sum,touch_apply i g s,← Finset.sum_sub_distrib]
  -- ensure expanded right touch g, not left
  refine Finset.sum_congr rfl fun j hj=>?_ ; rw [D_touch false _ _ _ _ h, touch_prod (p:=false),touched _ _ _ (HV j),he]; simp
end Rotor

variable [Algebra ℚ R]
lemma corresponds (u:Rotor s U)(h:Graded ρ false k)(H:Twin s W)(he : ∀ i∈s,∀ j∈s, let F:=varC R ρ i*varC R ρ j; U (touch k s F) []=(touch k s (U F)) []+W F []) : reflects U W k s:= by
  have hp : touch k s*U - U*touch k s = -W := by
    apply sub_eq_zero.mp; refine Twin.zero (s:=s) ?_ fun i hi j hj=> ?_
    · exact ((u.catches h).sub (by rw [← zero_sub]; exact Twin.none.sub H))
    specialize he i hi j hj; dsimp only at he; simp only [LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,sub_read,neg_read, he]; abel
  intro F; have h:=LinearMap.congr_fun hp F; simp only [LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply] at h; apply eq_add_of_sub_eq; -- target orientation?
  conv_rhs=> rw [eq_add_of_sub_eq h]
  abel

-- intertwine W.mul by H charge insertion. Assume T simplifies H. If U not homogeneous parity no issue here except when using cross powers below.
lemma charge (_h:Graded ρ false k)(H0:touch k s H=0)(he:Commute (tether false k s H) (touch k s)) (tv:FinRank H)(hf:FinRank F): wither k s (H*F) = H*wither k s F + cross false k s H (wither k s F):= by
  let v := LinearMap.mul R _ H; let M:=tether false k s H
  have ht: reflects v (-M) k s:=by
    intro G; change H*_ = touch k s (H*G)+ -cross false k s H G; rw [touch_prod (p:=false),H0]; simp
  have hu : H * wither k s F=wither k s (H*F) + -cross false k s H (wither k s F):= reflects_wither ht he.neg_left hf (tv.mul hf)
  rw [hu]; abel

omit [Algebra ℚ R] in
lemma curb (u:reflects U 0 k s): Commute U (touch k s):=LinearMap.ext fun F=> (u F).trans (by simp)
lemma shift_light (u:lever U.toAddMonoidHom)(hh:reflects U 0 k s)(H0:touch k s (U F)=0)(he:Commute (tether false k s (U F)) (touch k s)) (hU:Tone p (U F))(tv:FinRank (U F))
    (hv:Graded ρ false k)(hf:Tone false F)(hg:Tone false G)(fr: FinRank F)(np:IsNilpotent F)(N:IsNilpotent G)
    (H:exp (-G)=wither k s (exp (-F))) : U G = U F - cross false k s (U F) G := by
  let T:=U F; let e := exp (-G); let f := exp (-F)
  have ht F (h : Tone false F) (H : IsNilpotent F) : U (exp (-F))= exp (-F)*-(U F):= by rw [show U (exp (-F))=_ from swept u h.neg H.neg,map_neg]; rfl
  have heq: U f= -(T*f):= (ht F hf np).trans (by change f*(-T)=_; rw [hf.neg.exponent.skim (-T),neg_mul]);
  have hfE: FinRank f:=fr.neg.exponent
  have h0:= reflects_wither hh (Commute.zero_left _) hfE (heq.symm ▸ (tv.mul hfE).neg); change U (wither _ s f)=wither _ s (U f)+0 at h0
  have htG: U e=-(T*e+ cross false k s T e):=by
    rw [show e=wither k s f from H,h0,add_zero,heq, ← neg_one_smul R, wither_smul (tv.mul hfE), neg_one_smul, charge hv H0 he tv hfE]
  have hlast: cross false k s T e=e * -(cross false k s T G):=by dsimp only [e]; rw [cross_exp hg.neg hU hv N.neg, ← from_tether, map_neg]; rfl
  rw [hlast,← hg.neg.exponent.skim T,ht G hg N] at htG
  apply (isUnit_exp N.neg).mul_left_cancel; change e* _=e * _; rw [mul_sub]; rw [mul_neg,mul_neg,neg_inj] at htG; exact htG.trans (sub_eq_add_neg _ _).symm
end YM.MSBar.Bric.Coil
