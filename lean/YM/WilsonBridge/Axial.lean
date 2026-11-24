import YM.WilsonBridge.TreeFix
import YM.WilsonBridge.Substitution

/-!
# Projection of the actual master tensors to the cotree gauge

Perform the axial projection on the Fourier supplier's *position* alphabet.
Prove that the FP ghosts then contribute no interaction (after removing the free
quadratic). Statement at `Endμ`, without yet rewriting the Gaussian as moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit MS.Book
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Orbit.LogReal Orbit.Cog
open PertExtension Orb Lattice MS.Native MS.Bare Cylinder.Taylor Bare.Focus
open Function Finset
open scoped BigOperators Classical Topology ContDiff
variable {V : Type} [Fintype V] {q : Sector V}
variable (z : V→ℂ)
local notation "dM" => Matrix.diagonal z
lemma diag_drop (F:Raw V ℂ) (i:V): D i (pull dM F)=z i • pull dM (D i F) := by
    rw [pull_drop]; simp [Matrix.diagonal_apply,ite_smul]
omit [Fintype V] in
lemma diag_tie : Tie q q (Matrix.diagonal z : Matrix V V ℂ) := by
    intro i j; by_cases h:i=j; · intro _; rw [h]
    simp [Ne.symm h]
lemma diag_letter (i:V): pull dM (atLetter i) = z i • atLetter i:= by rw [pull_letter]; simp [Matrix.diagonal_apply,ite_smul]
lemma diag_ink {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (z:V→ℝ) (u:V→E) (L:E→ℝ) (h:germ L):
    pull (Matrix.diagonal ((fun i=>(z i:ℂ)))) (ink u L)=ink (fun i=> z i • u i) L := by
    rw [show Matrix.diagonal (fun i=>(z i:ℂ))=(Matrix.diagonal z).map ((↑):ℝ→ℂ) from (by ext i j; by_cases h:i=j<;>simp [h])]
    exact pull_ink _ u _ L h (fun i=> by simp [Matrix.diagonal_apply,ite_smul]) -- fix
lemma diag_cov (K:Grain V) (i j:V): cov_push K dM i j=z i*K i j*z j := by
    unfold cov_push; rw [Matrix.diagonal_transpose, Matrix.mul_diagonal,Matrix.diagonal_mul]; rfl -- names?

namespace Based.Position
variable {G:Gauge}{n:Side}
local notation "P"=> Position.Parity G n
local notation "ΠB" => Position.Bracket G n
local notation "L"=> Position.Letter G n
local notation "W"=> actionW G n
local notation "ν"=> Focus.launch (Position.glow G n) (colorTerm G (BasedSite n)) generator
local notation "S"=> mask 2 (actionW G n)

/-- Surviving letters. With FP ghosts reserved (`true`), retain K only on the tree. -/
def keep (w:Bool) (i:L): ℝ := match i with
    | Sum.inl (Sum.inl i)=> if Branch i.1 then 0 else 1
    | Sum.inr (Sum.inl i)=> if w=true ∧ Branch i.1 then 1 else 0
    | Sum.inl (Sum.inr _)=> if w=true then 1 else 0
    | Sum.inr (Sum.inr _) => 0
abbrev projection (G:Gauge)(n:Side)(w:Bool): Matrix (Letter G n) (Letter G n) ℂ:= Matrix.diagonal (fun i=> ((keep w i):ℂ))
local notation "Pt" => pull (projection G n true)
local notation "Pf" => pull (projection G n false)
local infixl:70 " ⋆ " => product (Position.Parity G n)

lemma Yoff (i:Gluon G n)(h:Branch i.1): covector i=0:= by
    apply LinearMap.ext; intro x; change projector i (insertCo G n x)=0; rw [projector_k (Q:=OEdge n)]; rw [co_off x (⟨i.1,h⟩:Trees n)]; rfl
lemma tree_cov_push (hn:Even n.val) : let K := (treeFix G hn).half; cov_push K (projection G n true)=K:= by
    intro K; suffices he: ∀ i j:L, ((keep true i):ℂ)* K i j * (keep true j:ℂ) = K i j from funext fun i=> funext fun j=> (diag_cov _ _ i j).trans (he i j)
    rintro ((i|i)|(i|i)) ((j|j)|(j|j))
    all_goals try solve| simp only [K, Kinetics.Fixing.half,Kinetics.Fixing.chill,mul_zero,zero_mul]
    -- AA, cK, Kc
    · change _ * ((1/2:ℂ) * (AAcov hn i j:ℂ)) * _=((1/2:ℂ)*(AAcov hn i j:ℂ))
      by_cases h:Branch i.1
      · simp_rw [AAcov,Yoff i h]; simp
      by_cases hv:Branch j.1
      · simp [AAcov,Yoff j hv]; -- check map_zero
      rw [keep,if_neg h,keep, if_neg hv]; simp
    · by_cases h:Branch j.1
      · simp_rw [keep,true_and, if_pos h]; simp
      · change _ * ((1/2:ℂ)* -( ( projector i (Y G hn (priv j)):ℝ):ℂ)) * _ = (1/2:ℂ)* -( ( projector i (Y G hn (priv j)):ℝ):ℂ)
        rw [off_y hn j h]; simp
    by_cases h:Branch i.1
    · simp_rw [keep,true_and, if_pos h]; simp
    · change _ * ((1/2:ℂ)*( ( projector j (Y G hn (priv i)):ℝ):ℂ)) * _ = (1/2:ℂ)*( ( projector j (Y G hn (priv i)):ℝ):ℂ)
      rw [off_y hn i h]; simp

lemma ink_only (F:E G n→ℝ)(h:germ F): Pt (ink (Position.glow G n).e0 F)=Pf (ink (Position.glow G n).e0 F):= by
    change pull (Matrix.diagonal _) _=pull (Matrix.diagonal _) _; rw [diag_ink (keep true) _ F h,diag_ink (keep false) _ F h]; congr 1; ext1 i; rcases i with (i|i)|(i|i) <;> first| rfl | (change _ • (0:E G n) = _ • (0:E G n); simp)

private def clearTree : E G n →L[ℝ] E G n := ((insertCo G n).comp (co G n)).toContinuousLinearMap
private lemma clears (F:E G n)(x:OEdge n) : clearTree F x= if _h:¬Branch x then F x else 0:= rfl
private lemma direction_tree (i:L): keep true i • (Position.glow G n).e0 i=clearTree ((Position.glow G n).e0 i):= by
    rcases i with (i|i)|(i|i) <;> try (change _ • (0:E G n)=clearTree 0; rw [map_zero,smul_zero])
    funext j; change (if Branch i.1 then (0:ℝ) else 1) • ((priv i:E G n) j)=_
    change _=clearTree (priv i) j; rw [clears]; by_cases he:i.1=j
    · subst j; split_ifs<;> simp [*]
    split_ifs<;> simp [priv,Ne.symm he]

lemma fp_local (i:Gluon G n)(hi:Branch i.1) :
    Pt (stone (Position.glow G n) generator i) = ∑ j:Ghost G n, ((chargeX i j):ℂ) • atLetter (c j) := by
    let T:= Position.glow G n; unfold stone; rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_) ; let F:=projector i ∘ generator j
    change Pt (atLetter (c j) ⋆ ink T.e0 F)=_
    have hf : germ F:= winds.vectorSeed T i j
    rw [pull_prod _ (diag_tie _),diag_letter,show (keep true (c j):ℂ)=1 from Complex.ofReal_one,one_smul, diag_ink (keep true) T.e0 F hf, funext direction_tree]; change atLetter (c j) ⋆ ink (clearTree ∘ T.e0) F= _; rw [← show ink T.e0 (F ∘ clearTree)= _ from (ink_ctrl_one T.e0 clearTree hf)]; rw [show F ∘ clearTree=(fun _:E G n=> F 0) from ?_]; swap
    · funext x; unfold F comp; simp_rw [projector_k (Q:=OEdge n),gen_at,clears,dif_neg (not_not.mpr hi)]; rfl
    rw [ink_const, ← (coin_pure (p:=P) _).central, coin_product]; rfl

local notation "Q" => FreeBV.interaction W (haarW G n)
lemma rank_ghost (i:ℕ) (h:0 < i): mask (i+2:ℤ) (Pt ((ΠB).hung ν))=0:= by
    rw [Bonded.hung,map_sum,map_sum]; refine Finset.sum_eq_zero (fun j _=>?_); simp_rw [map_smul, pull_prod _ (diag_tie _),diag_letter]; rcases j with j|j
    · change (1:ℂ) • mask _ ((((keep true (k j)):ℂ) • atLetter (k j)) ⋆ Pt (stone (Position.glow G n) generator j))=0 -- remove a
      by_cases hx:Branch j.1; swap; · simp [keep,k,hx,LinearMap.zero_apply]
      have hv : (((keep true (k j) :ℝ)):ℂ)=1:= by simp [keep,hx]
      have ht : rank (1+1) (atLetter (k j) ⋆ (Pt (stone (Position.glow G n) generator j))) := by rw [fp_local _ hx]; exact (rank_letter _).product (Rails.sum _ (fun i _=> Rails.smul _ (rank_letter _)))
      rw [fp_local j hx] at ht -- maybe not desired
      rw [hv, one_smul,one_smul, fp_local j hx, rank_off ht (by omega)]
    change _ • mask _ (((0:ℂ) • atLetter (b j)) ⋆ Pt _)=0; simp
lemma no_ghost : Pf ((ΠB).hung ν)=0:= by
    rw [Bonded.hung,map_sum]; refine Finset.sum_eq_zero fun j _=> ?_; rw [map_smul, pull_prod _ (diag_tie _), diag_letter]; rcases j with j|j <;> (change _ • (((0:ℂ) • _) ⋆ _)=0; simp)
lemma same_body : pointL ℕ Pt Q=pointL ℕ Pf Q:= by
    funext i; by_cases hi:i=0
    · subst i; change Pt (Q 0)=Pf (Q 0); rw [FreeBV.MasterLaw.initial_zero]; simp
    have he : Q i= mask (i+2:ℤ) W + mask (i+0:ℤ) (haarW G n):= by
        unfold FreeBV.interaction FreeBV.relative; rw [Pi.sub_apply, SplitP.refineV,if_neg (show i≠useN.origin from hi),sub_zero]; rfl
    change Pt (Q i)=Pf (Q i); simp_rw [he,map_add,pull_mask]; unfold actionW Sourced; simp_rw [map_add,no_ghost,map_zero, ink_only _ (expGerm ..),rank_ghost i (Nat.pos_of_ne_zero hi),add_zero, haarW, ink_only _ haarSmooth]

def real_cov (i:L): Orb.Source G n:= match i with
    | Sum.inl (Sum.inl i) => covector i
    | _=> 0
def noFP (G:Gauge)(h:Even n.val) : Grain (Letter G n):= fun i j=> (1/2:ℂ)* (real_cov i ((saddle h).inverse (real_cov j)):ℝ)
lemma tree_cov_false (hn:Even n.val) : cov_push (treeFix G hn).half (projection G n false)=noFP G hn:= by
    suffices he : ∀ i j:L, ((keep false i):ℂ)* (treeFix G hn).half i j * (keep false j:ℂ) = noFP G hn i j from funext fun i=> funext fun j=> (diag_cov _ _ i j).trans (he i j)
    rintro ((i|i)|(i|i)) ((j|j)|(j|j))
    · exact (diag_cov (fun x:L=>((keep true x):ℂ)) (treeFix G hn).half (a i) (a j)).symm.trans (congr_fun (congr_fun (tree_cov_push (G:=G) hn) (a i)) (a j)) -- K compare
    all_goals simp [noFP, real_cov,keep]

variable (he:Even n.val) {O:Wilson.Config G n→ℝ}{d:ℤ}
include he
lemma computed_tree (h:germ (charted O)) (c:ℕ→ℂ): Endμ (treeFix G he).half P Q (rankLevel d (insertion O)) c ↔ Endμ (noFP G he) P Q (rankLevel d (insertion O)) c:= by
    let R:= insertion O; let F:= rankLevel d R; let K:= (treeFix G he).half
    have H := FreeBV.MasterLaw.supported (Position.master (G:=G) (n:=n)) -- namespace
    have hv : Γ F P := FreeBV.basis_level (ink_s _ (Position.glow G n).never h)
    have heq1:= pull_end (projection G n true) Q F (tree_cov_push he) H hv (diag_tie (q:=P) _) c
    have heq2:= pull_end (projection G n false) Q F (tree_cov_false he) H hv (diag_tie (q:=P) _) c
    have hp : pointL ℕ Pt F=pointL ℕ Pf F:= by funext i; change Pt (mask _ R)=Pf (mask _ R); simp_rw [pull_mask]; rw [show Pt R=Pf R from ink_only _ h]
    rw [hp,same_body] at heq1; exact heq1.symm.trans heq2
end Based.Position
end YM.WilsonBridge
