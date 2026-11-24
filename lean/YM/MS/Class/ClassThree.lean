import YM.MS.Class.VectorCube
/-!
# Classification at rank three assembled. `Mark.token` is the single read.
Use actual unit-tangent coefficient later (from lowest-order cubic).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect.Mark
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open scoped Topology ContDiff
open Complex (I)
variable {G: Gauge} {F H: Law G} {h:ℤ}

lemma by_size (X: Class F h) (hh:h≤4) (hq : ∀ (w : Legs (Lane4 G)), net w=0 → fieldDim ghostNo w=0 → fieldDim wfield w ≤4 → w.length=3 → F w=0) : EqualAt 3 F 0:= by
    intro w hw hp; by_cases he:fieldDim ghostNo w=0; swap; exact X.ne _ hw he
    rcases lt_or_ge 4 (fieldDim wfield w) with h|h; exact X.tall _ hw (lt_of_le_of_lt hh h)
    exact hq w hw he h hp

lemma body_zero (X:Class F h) (H : ∀ i j k, token F i j k=0) (hh:h≤4) (a b c i j k p q r) (h : net [W a i p,W b j q,W c k r]=0): F [W a i p,W b j q,W c k r]=0:=by
    have hv : r= -(p+q):= by simpa [net,W,qnote, ←add_assoc, add_eq_zero_iff_eq_neg', eq_comm] using h
    subst r; exact steer_vanish X H hh i j k a b c (p,q)
lemma token_zero (X:Class F h) (H : ∀ i j k, token F i j k=0) (hh:h≤4) i j k p q r (hl:net [S i p,C j q,C k r]=0): F [S i p,C j q,C k r]=0:= by
    rw [token_constant X hh _ _ _ _ _ _ (by simpa [net,S,C,qnote] using hl),H]
private lemma perm_zero (X : Class F h) {l k : List (Lane4 G)} (hw: l.Perm k) (hZ:net l=0) (hz:net k=0→ F k=0): F l=0:= Class_zero X hw hZ (hz ((hw.map Prod.snd).sum_eq.symm.trans hZ))
-- for any permutation of the triple. Proof by real enumeration only of 4 roles; budgets finite.
set_option maxHeartbeats 600000 in
lemma triple_zero (X:Class F h) (H : ∀ i j k, token F i j k=0) (hh:h≤4) : EqualAt 3 F 0 := by
   refine by_size X hh ?_
   intro w hw h1 h2 hk
   -- roles
   obtain ⟨l,m,r,rfl⟩:= List.length_eq_three.mp hk
   rcases l with ⟨⟨⟨_|a,_|_⟩,i⟩,p⟩ <;> rcases m with ⟨⟨⟨_|b,_|_⟩,j⟩,q⟩ <;> rcases r with ⟨⟨⟨_|c,_|_⟩,k⟩,r⟩ <;>
       norm_num [fieldDim, wfield,ghostNo,ghostChannel,dim] at h1 <;> norm_num [fieldDim,wfield,dim] at h2
   -- cases; solve with propagation along selected permutation
   all_goals first | exact body_zero X H hh _ _ _ _ _ _ _ _ _ hw | exact token_zero X H hh _ _ _ _ _ _ hw | exact ping_zero X H hh _ _ _ _ _ _ _ _ hw | skip
   all_goals first
    | exact perm_zero X (List.Perm.swap ..) hw (token_zero X H hh _ _ _ _ _ _)
    | exact perm_zero X (List.Perm.swap ..) hw (ping_zero X H hh _ _ _ _ _ _ _ _)
    | exact perm_zero X ((List.Perm.swap ..).cons _) hw (token_zero X H hh _ _ _ _ _ _)
    | exact perm_zero X ((List.Perm.swap ..).cons _) hw (ping_zero X H hh _ _ _ _ _ _ _ _)
    | exact perm_zero X (((List.Perm.swap ..).cons _).trans (List.Perm.swap ..)) hw (token_zero X H hh _ _ _ _ _ _)
    | exact perm_zero X (((List.Perm.swap ..).cons _).trans (List.Perm.swap ..)) hw (ping_zero X H hh _ _ _ _ _ _ _ _)
    | exact perm_zero X ((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)) hw (token_zero X H hh _ _ _ _ _ _)
    | exact perm_zero X ((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)) hw (ping_zero X H hh _ _ _ _ _ _ _ _)
    | exact perm_zero X (((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)).trans (List.Perm.swap ..)) hw (token_zero X H hh _ _ _ _ _ _)
    | exact perm_zero X (((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)).trans (List.Perm.swap ..)) hw (ping_zero X H hh _ _ _ _ _ _ _ _)
lemma class_three (X:Class F 4) (Y:Class H 4) (K : G.Simple) (v:ℝ) (hv:v≠0) (hx : ∀ i j k, token H i j k=(LieColor i j k:ℂ)*(v:ℂ)) :
    ∃ z:ℝ, EqualAt 3 F ((z:ℂ) • H):= by
   obtain ⟨c,_,hc⟩:= lie_token X (le_refl 4) K
   let z:=c/v; have he : v*z=c:= by unfold z; field_simp
   refine ⟨z,fun w hw h=> sub_eq_zero.mp (triple_zero (X.sub (Y.scalar z)) (fun i j k=> ?_) (le_refl 4) w hw h)⟩
   change token F i j k-(z:ℂ)*token H i j k=0; rw [hx,hc,←he,Complex.ofReal_mul]; ring
lemma lower_three (X:Class F h) (he:h<4) : EqualAt 3 F 0:= triple_zero X (fun i j k=> X.tall _ (by simp [S,C,qnote,net]) he) he.le
end YM.MS.Landau.Detect.Mark
