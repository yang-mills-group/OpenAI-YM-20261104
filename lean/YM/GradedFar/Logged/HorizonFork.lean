import YM.GradedFar.Logged.Seats

/-!
# (G.4) actual log-fork estimates at every viewer

Uses LogTrace at its Project mathematical meaning and Section B choice. Not proof
it is earned. This is the full-near log budget, even moving Far. Economy is at
*physical* fields (calls without H-dependence); this thesis can fund even full
proper subword requests. Need still the `H` budget theorem & G.8 when applying later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open Tree Tree.Node Seats
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {I J:Type}[Fintype I][Fintype J] {P:Prescription F.sector.derivatives}
local notation "nearSet"=>Tree.near I J
local notation "outerSet"=>Tree.outer I J
local notation "tree"=>Tree.frame I J
local notation "bare"=> Stage.bare
local notation "X"=>Tree.position

/-- Terracing r,s positive in this order. `x,y` shapes. -/
structure Landed (r t M δ:ℝ)(x:I→E4)(y:J→E4): Prop where
    fresh : 0<r
    posed : r≤t
    pays : ∀ i: I, ‖x i‖≤M
    outer : ∀ j:J, ‖y j‖≤M
    apart : ∀ j:J, 2*δ ≤ ‖y j‖
    xnot : ∀ i j,i≠j→δ≤‖x i-x j‖
    ynot : ∀ i j,i≠j→δ≤‖y i-y j‖
    space : r*M ≤ t*δ

section
variable {r t M δ:ℝ} {x:I→E4}{y:J→E4}
theorem separated (s:ℝ) (v:I→E4) (o:E4) (h:0<s) (hp:0<δ) (hx:∀ i j,i≠j→δ≤‖v i-v j‖) : Injective (homing s o v):= by
    intro i j hi; obtain eq:= smul_right_injective E4 h.ne' (show s • v i=s • v j from add_left_cancel hi); by_contra H; have hp:=hp.trans_le (hx i j H); rw [eq,sub_self,norm_zero] at hp; linarith

variable (h: Landed r t M δ x y) (o:E4) (hd:0<δ)
include h hd
lemma unique_part : Injective (beside (homing r o x) (homing t o y)) := by
    have ht:=h.fresh.trans_le h.posed
    refine beside_distinct.mpr ⟨separated _ x o h.fresh hd h.xnot,separated _ y o ht hd h.ynot,?_⟩
    intro i j hv
    have he : ‖r • x i‖= ‖t • y j‖ := congrArg norm (show _=_ from add_left_cancel hv)
    rw [norm_smul, norm_smul,Real.norm_of_nonneg h.fresh.le,Real.norm_of_nonneg ht.le] at he
    have hs:= mul_le_mul_of_nonneg_left (h.apart j) ht.le; have hp:= h.space; have hh:=mul_le_mul_of_nonneg_left (h.pays i) h.fresh.le
    nlinarith only [he,hs,hp,hh, mul_pos ht hd]
lemma unique_root : Injective (beside (sole o) (homing t o y)) := by
    have ht:=h.fresh.trans_le h.posed
    refine beside_distinct.mpr ⟨injective_of_subsingleton _,separated _ y o ht hd h.ynot,?_⟩
    intro i j hh
    have hu : y j=0 := by
      apply smul_right_injective E4 ht.ne'; dsimp only; rw [smul_zero]; apply add_left_cancel (a:=o); rw [add_zero]; exact hh.symm
    have he:=h.apart j; rw [hu,norm_zero] at he; linarith only [hd,he]
end

section
variable (bank : LogTrace F P)(simple:G.Simple) (p:I→C.book.Token)(q:J→C.book.Token)
    (h:ℕ) {M δ:ℝ}(hm:0≤M)(hd:0<δ)
local notation "p'"=> named p q
def size (r t:ℝ):ℝ:= r^(sigma p)*t^(sigma q)
omit bank simple in
lemma tree_size (r t:ℝ) : size p q r t= Tree.mass p' r t:=rfl
abbrev SAt (s:Viewers F)(r t:ℝ)(x:I→E4)(y:J→E4)(o:E4) := observe (spectator F s) (beside (homing r o x) (homing t o y)) (beside p q)
include bank simple hm hd

/-- G.4, in true token fields. Price not normalized H. Exponents don't even
know the later choice B. -/
theorem price_pair : ∃ (k:ℕ) (b:ℝ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀ (r:ℝ)(x:I→E4)(z:J→E4)(o:E4), Landed r t M δ x z → ∀ v:Viewers F,
    size p q r t * ‖SAt F p q v r t x z o - P.truncated (spectator F v) h (homing r o x) p o (homing t o z) q‖ ≤
      b*(badge t*badge r)^k * (t+(r/t)^(h+1)) := by
    obtain ⟨C,k,hc,hW⟩:= Full.main F simple bank p' h hm hd; refine ⟨k,C,hc,hW.mono fun t hT r x z o H v=> ?_⟩
    rw [tree_size, ← Seats.old_read F x z o r t p q v (unique_root H o hd), SAt,← Seats.demand F x z o r t p q v (unique_part H o hd)]
    exact hT r x z o H.fresh H.posed H.pays H.outer H.apart H.xnot H.space H.ynot v

/-- And the phase discrepancy (same unit-price as in G.4). -/
theorem price_phase : ∃ k:ℕ, ∀ᶠ t:ℝ in 𝓝[>]0,∀ (r:ℝ)(x:I→E4)(z:J→E4)(o:E4), Landed r t M δ x z → ∀ v:Viewers F,
    size p q r t * ‖SAt F p q v r t x z o - SAt F p q none r t x z o‖ ≤ 2*(badge t*badge r)^k * t := by
  obtain ⟨k,hV⟩:= Stage.full F bank p' hm hd; refine ⟨k,hV.mono fun t hT r x z o H v=>?_⟩
  let D q' := flux P (spectator F q') (tree).leaves (X r t x z o) p' base (bare:Fin 0 → E4) bare 0
  have hh q' : size p q r t * ‖D q'‖ ≤ t*(badge t*badge r)^k:= hT r x z o H.fresh H.posed H.pays H.outer H.apart H.xnot H.space H.ynot _
  rw [SAt,SAt,← Seats.demand F x z o r t p q v (unique_part H o hd),← Seats.demand F x z o r t p q none (unique_part H o hd)]
  rw [show Full.demand F v (X r t x z o) (tree).leaves p'-Full.demand F none (X r t x z o) (tree).leaves p'=D v-D none by unfold D Full.demand; simp_rw [VAC.difference F simple]; abel]
  have hk:= mul_le_mul_of_nonneg_left (norm_sub_le (D v) (D none)) (show 0≤ size p q r t from mul_nonneg (pow_nonneg H.fresh.le _) (pow_nonneg (H.fresh.le.trans H.posed) _))
  nlinarith only [hk, hh v, hh none]
end
end YM.OPE.Logged.Fork
