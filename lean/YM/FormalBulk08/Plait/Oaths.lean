import YM.FormalBulk08.Plait.Opal

/-! At same Hessian codomain, center after translation with identity linear
active part. Infer Hessian B0 directly from regular orbit Ward. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Filter Wick Orb Series Jets PowerSeries
open Matrix (of)
open scoped BigOperators Topology Classical Matrix ContDiff
variable {V I R:Type*} [Fintype V][Fintype I][DecidableEq V] [CommRing R]

def unmixed (I:Type*): I→Pap I:= fun i=> C (MvPolynomial.X i)
omit [Fintype V] [DecidableEq V] [Fintype I] in lemma dish_id (p: Pap (V⊕I)): dish (still V I) (unmixed I) p=p:= by
   unfold dish;rw [show Sum.elim _ _=(fun i:V⊕I=> C (MvPolynomial.X i : TypeR (V⊕I))) from funext fun i=>by cases i <;> simp [still,unmixed,upstream],virgin]
omit [Fintype V] [DecidableEq V] in lemma roll_eff {R S:Type*}[CommRing R][CommRing S][Algebra R S](p:Plate R V) (t:V→PowerSeries S): coeff 0 (roam R t p)=MvPolynomial.aeval (fun i=>coeff 0 (t i)) (coeff 0 p):= by rw [←roam_level t,roam,change_coeff_zero, change_coeff_zero];rw [coeff_zero_C]
lemma trident (p:Glyphs R V)(u: V→R)(i:V): MvPolynomial.pderiv i (MvPolynomial.aeval (tilt u 1) p)= MvPolynomial.aeval (tilt u 1) (MvPolynomial.pderiv i p):= by
   rw [pick_grad (tilt u 1)];simp_rw [tilt_grad];simp [Matrix.one_apply,ite_mul,apply_ite MvPolynomial.C]
omit [Fintype V] [DecidableEq V] [Fintype I] in
lemma skip_teleport (p:Ink V I): teleport (unmixed I) p=p:= by
   unfold teleport; rw [show tri (unmixed I) V=C.comp (RingHom.id _) from ?_,pure_map];simp
   ext <;> simp [tri,unmixed,boost]
variable (T:Hull V I){p:Pap (V⊕I)}(h:Solved T p){S L:Jets.Rays (V⊕I)→ ℝ}
   (hs:ContDiffAt ℝ ∞ S 0)(hL:L 0=0) {y:V→Ink V I}
include h hs hL
lemma key_change (e:Elan (originH T.saddle S) T (baseP S L) p (unmixed I) (unmixed I) y 1 1) : dimR (gateP S) 0=T.saddle.P:= by
    have he:=congr_arg (coeff 0) e.speech
    let V':= toInk (originH T.saddle S) (baseP S L); let q:= variation T.saddle I
    rw [map_add,covelog_rank (weight_jac y 1 1 e.origin e.invert),←teleport_toInk,←teleport_toInk,skip_teleport,skip_teleport] at he;change coeff 0 V'=coeff 0 (roam (TypeR I) _ (toInk T p))+0 at he;rw [add_zero,roll_eff,h] at he
    obtain ⟨u,hu⟩:=e.origin;unfold V' at he; simp_rw [hu] at he; rw [veget,cube_base,show chord (paste L) 0=0 by rw [chord,paste_first,hL,map_zero,map_zero], add_zero, Nat.zero_add] at he
    have hx: q.Pᵀ=q.P:= by ext1 i j;exact q.valid j i
    ext1 i j; have ht:= congr_arg (MvPolynomial.pderiv i) (congr_arg (MvPolynomial.pderiv j) he)
    change MvPolynomial.pderiv i (MvPolynomial.pderiv j (-chord (paste S) 2)) = MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.aeval (tilt u 1) (rect q.P+ MvPolynomial.C T.main))) at ht
    rw [trident,trident] at ht; simp only [map_add,MvPolynomial.pderiv_C,add_zero,map_neg] at ht; rw [rect_cease hx i j, map_neg,MvPolynomial.aeval_C,chord_sight S hs i j, neg_inj] at ht -- norm cast detail
    change gateP S i j 0=T.saddle.P i j; exact MvPolynomial.C_injective (σ:=I) ℝ ((paste_first (gateP S i j)).symm.trans (MvPolynomial.C_injective (σ:=V) (TypeR I) ht))
end YM.FormalBulk08.Plait
