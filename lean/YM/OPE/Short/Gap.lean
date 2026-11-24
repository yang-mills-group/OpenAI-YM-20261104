import YM.OPE.Sparse.Endpoint
/-!
# The first filtered-mass gap: upgrade via unavailable channels

The use of ``gap'' here is in the *finite engineering dimensions* only,
NOT a mass-gap claim. Literal physical fields from below weight 4 lie on the
identity line (rank of the comparative free table and equality of finite
ranks). Applying the same true prescription at horizon-3 in the hierarchy,
one can therefore improve its complete remainders through horizons 0,1,2
without any loss when every secondary ratio still exceeds a fixed power of
the root. General depths, weights and labels; all phases on the common U. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Extraction
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple)
local notation "Q"=>U.sector.derivatives

include hG X U
lemma unit_field {m:ℕ}(hm:m < 4)(z:S.Field m):∃ c:ℂ,c • S.unit m=z:= by
    let A:= Module.finrank ℂ (S.Field m)
    have ht := YM.UVNext.FreeStress.dim_before C.book.grid hG hm
    have hf : A=1:=((X.U 0 m).symm).finrank_eq.trans ht
    exact (finrank_eq_one_iff_of_nonzero' (S.unit m) (S.alive m U.room.kernel.laws)).1 hf z

-- Stage and transport proofs after

lemma low_annihilator {m:ℕ}(h₁:0 < m)(h₂:m<4)(x:S.Field m)(hz:x∈R.stratum m):x=0:=by
    obtain ⟨c,rfl⟩:=unit_field U X hG h₂ x
    have hi:= (Q).fixs R.lifts R.continuum.laws (Nat.zero_le m)
    rw [← R.test_fixes m (c • S.unit _) hz,← hi,map_smul,R.cut_rise m 0 m (Nat.zero_le m),R.kills_lower m 0 h₁,smul_zero] -- check .. arguments

lemma no_channels {m:ℕ}(hm:0 < m)(hn:m<4): IsEmpty (R.channels m):=by
  constructor; intro i
  apply (R.basis m).ne_zero i
  exact Subtype.ext (low_annihilator U R X hG hm hn _ (R.basis m i).property)

namespace Bottom
variable {I J:Type}[Fintype I][Fintype J](v:I→S.Tag)(w:J→S.Tag)
lemma fewer(d:ℕ)(h:d≤3)(x:I→E4)(y:J→E4)(o:E4)(T):trunc T U R d x o (voices v) y (voices w)=trunc T U R 3 x o (voices v) y (voices w):=by
    let g(d:ℕ):= ∑ i:R.channels d,(R.coef d i x (voices v) o) * whole (S:=S) T (sole o) (sole (R.actor d i):Labels S (fun _:Unit=>d)) y (voices w)
    have h₁(j:ℕ)(hj:j≤3) : trunc T U R j x o (voices v) y (voices w) = g 0 :=by
        apply Eq.trans (@Finset.sum_eq_single _ _ _ Finset.univ (fun i:Fin (j+1)=>g i) (⟨0,Nat.succ_pos _⟩) _ (by simp)) rfl
        intro k hm he'; have hk:k.val≠0:=fun he=>he' (Fin.ext he)
        haveI := no_channels U R X hG (Nat.pos_of_ne_zero hk) ((Nat.lt_succ_of_le (Nat.le_of_lt_succ k.isLt|>.trans hj)):k.val<4)
        exact Finset.sum_eq_zero (fun i _=>(IsEmpty.false (α:=R.channels k.val) i).elim)
    exact (h₁ d h).trans (h₁ 3 le_rfl).symm

lemma unchanged(r:Viewers U)(d:ℕ)(h:d≤3)(x:I→E4)(y:J→E4)(o:E4): formula U R x o (voices v) y (voices w) d r=formula U R x o (voices v) y (voices w) 3 r:=by unfold formula; rw [fewer U R X hG v w _ h]
end Bottom
namespace Large
variable {n:ℕ}{f:Fin n→Nesting.Tree}
local notation "tree"=> Nesting.Tree.fork n f
abbrev Below {n:ℕ}{f:Fin n→Nesting.Tree} := Measuring.Tree.Nonroot f

def Moderated(x:ℝ)(s:(fork n f).Inner→ℝ)(A:ℝ):= ∀ p:Below (f:=f),x^A ≤ _root_.YM.OPE.Nesting.Tree.ratios tree 1 s (Sum.inr p) -- cannot use notation as identifier

omit U X hG in
private lemma annular (A:ℝ)(hA:(0:ℝ)≤ A)(d: (fork n f).Leaf→ℝ){D:ℕ}(hD:D≤3): ∃ ε:ℝ,0<ε ∧ ∀ x:ℝ, x∈Ioc 0 1 → ∀ s:(fork n f).Inner→ℝ, s (Sum.inl ())=x→Moderated x s A→ toll d ε 4 s ≤ toll d 0 D s :=by
    let k:ℝ:=Fintype.card (Below (f:=f))
    have hk:0≤k:=by unfold k; exact Nat.cast_nonneg _
    let α:ℝ:=(1+A*k)
    let ε:=1/(2*α); have hα:0<α:=by dsimp [α]; positivity
    have heps:0<ε:=div_pos zero_lt_one (by positivity)
    have h: k*(A*(-ε)) = ε-1/2:=by have he:α*ε=1/2:=by dsimp [ε]; field_simp
                                   dsimp only [α] at he; linarith only [he]
    refine ⟨ε,heps,fun x hx s hs hp=>?_⟩
    let r (j:Below (f:=f)):=_root_.YM.OPE.Nesting.Tree.ratios tree 1 s (.inr j)
    let y (j:Below (f:=f)):ℝ:=r j^(-(tree|>.headSum d (.inr j))-0)
    have hr j:=show 0<r j from (Real.rpow_pos_of_pos hx.1 A).trans_le (hp j)
    unfold toll; simp_rw [hs]
    change x^(4-_-ε) * ∏ j:Below (f:=f), r j ^ (-(Nesting.Tree.headSum tree d (.inr j))-ε) ≤ x^(D-(∑ i,d i)-0)*(∏ j,y j)
    have ht(j): r j ^ (-(Nesting.Tree.headSum tree d (.inr j))-ε) ≤ (x^(A*(-ε))) * y j:=by
        rw [show -_-ε=(-ε)+(-_-0) by ring, Real.rpow_add (hr j)]; unfold y
        exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx.1 A) (hp j) (by linarith : -ε≤0)).trans_eq ((Real.rpow_mul hx.1.le _ _).symm)) (Real.rpow_nonneg (hr j).le _)
    refine (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _=> Real.rpow_nonneg (hr j).le _) (fun j _=>ht j)) (by exact Real.rpow_nonneg hx.1.le _)).trans ?_
    rw [show ∏ i, x ^ (A * -ε) * y i = _ from (Finset.prod_mul_distrib (f:=fun _=>x^(A * -ε)) (g:=y) (s:=Finset.univ)),← mul_assoc]
    apply mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun j _=> Real.rpow_nonneg (hr j).le _)
    rw [Finset.prod_const,Finset.card_univ,← Real.rpow_mul_natCast hx.1.le,show ↑(Fintype.card (Below (f:=f))) = k from rfl,(show (A*(-ε))*k= ε-1/2 from by linarith only [h]),← Real.rpow_add hx.1]
    apply Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2; linarith only [show (D:ℝ) ≤ 3 from (Nat.cast_le (α:=ℝ)|>.2 hD).trans_eq (by norm_num)]


include hG X U
lemma residue {M η δ:ℝ}(v:(fork n f).Leaf→S.Tag) (A:ℝ)(hA:0≤ A) (D:ℕ)(hD:D≤2) {J:Type}[Fintype J](w:J→S.Tag)
     (h:Services C F S)(hM:0≤M)(hη:0<η)(hδ:0<δ):
 ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→E4,Accept x M η s z→ Buffer z y δ → Moderated x s A→let b:=toll (wages v) 0 (D+1:ℕ) s; ‖Kernel.normData U R z v D y w‖ ≤ b ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q D y w‖ ≤ b:=by
    obtain ⟨ε,hε,hC⟩:=annular (f:=f) A hA (wages v) (show D+1≤3 by omega)
    filter_upwards [(uniform U R h).tested n f J v w 3 M η ε δ hM hη hε hδ,eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx he s z y hS hB hb
    obtain ⟨h_room,ha,hs⟩:= hx s z y hS hB
    let c:= toll (wages v) (0:ℝ) (D+1:ℕ) s
    have hP_ht:(↑(3:ℕ):ℝ)+1=4:=by norm_num
    have hP(q:Viewers U) : ‖Kernel.pipe U R z v q D y w‖ ≤ c:=by unfold Kernel.pipe; rw [Bottom.unchanged U R X hG v w q D (hD.trans (by norm_num))]; exact (hs q).trans (hP_ht.symm ▸ hC x ⟨(hS.levels.positive (.inl ())|>.trans_eq hS.scale), he⟩ s hS.scale hb)
    refine ⟨(glance_contract U ((norm_nonneg _).trans (hP none))|>.2 (fun q:Viewers U=>(congr_arg norm ( formula_seen U R _ _ _ y (voices w) D _ h_room.2.1 h_room.2.2)).trans_le (hP q))),hP⟩ -- w voices fix
end Large
end YM.OPE.Short
