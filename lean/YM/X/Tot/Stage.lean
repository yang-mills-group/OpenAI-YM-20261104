import YM.X.Tot.Leash
/-!
# little-root order. Duty milk and pinned momentum in hats. Need cutoff sequence C.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}
section budget
variable {p:poly V}{Q:Symmetric V}
-- derivative duty via exp envelope. tri eq lumps. handles degree zero.
lemma slit_budget (v:V→ℂ)(h:duty p (k+1)): duty (slit v p) k:= by
   rw [p.as_sum,map_sum]; refine duty.costs _ (fun i hi=>?_); rw [show monomial i (coeff i p)=coeff i p • monomial i (1:ℂ) from (by rw [←map_smul,smul_eq_mul,mul_one]),Derivation.map_smul]; apply duty.scalar; obtain ⟨p₀,hp⟩:= Common.letter i; rw [hp,renew]; apply duty.costs _; intro t _; apply duty.scalar; apply duty.more (duty.toll ..); simp; have h:= (le_totalDegree hi).trans h; omega
lemma slit_null (v:V→ℂ)(h:duty p 0): slit v p=0:= by have hh:totalDegree p=0:= Nat.eq_zero_of_le_zero h; rw [totalDegree_eq_zero_iff_eq_C] at hh; rw [hh]; exact slit_C ..
lemma multi_budget3 (h:duty p k)(x y z: V→₀ℂ): duty (multi Q p (glyph x*(glyph y*glyph z))) k:= by
    rw [m3]; cases k with
    | zero=> unfold edge; simp_rw [slit_null _ h,map_zero,mul_zero,add_zero]; exact duty.zero
    | succ k=>
       have hc(x:V→₀ℂ): duty (edge Q x p) k:= slit_budget _ h
       apply duty.add
       · repeat' apply duty.add
         all_goals (first | (rw [← Nat.add_comm 1]; exact duty.mul (leafy.mp (HCglyph _) ▸ Heat.Top.cut_bound _ _) (duty.slit_p (hc _))) | done)
       exact ((hc x).slit_p.slit_p).more (by omega)
lemma multi_budget (h:duty p k){A:poly V}(hh:HC A 3): duty (multi Q p A) k:= by
    change duty (toned Q p A) k; rw [A.as_sum,map_sum]; refine duty.costs _ (fun i hi=>?_); rw [show monomial i (coeff i A)= coeff i A • monomial i (1:ℂ) from (by rw [←map_smul,smul_eq_mul,mul_one]),map_smul]; apply duty.scalar; obtain ⟨v,hv⟩:= Common.letter i; rw [hv]; generalize hx:i.sum (fun _ k=>k)=n at v hv ⊢; have hn : n=3:= hx ▸ (Heat.Top.degree_eq i).symm.trans (hh (mem_support_iff.mp hi)); clear hx; subst n; rw [glyphs,Fin.prod_univ_succ,Fin.prod_univ_two];
    have he(v:V): X (R:=ℂ) v= glyph (Finsupp.single v 1):= by rw [glyph,Finsupp.linearCombination_single,one_smul]
    simp_rw [he]; exact multi_budget3 h _ _ _
end budget
-- normalized Tot.reference; common fire mask
abbrev mask (q:ℕ+)(χ:Floor R)(k:ℕ): Curly G:= fireMask (Floor.maskL q χ k)
def pillar (G:Gauge):Curly G:= ∑ p:PlaqAxes, vertex p
lemma pillar_type : pillar G∈tripleSpan G:= (tripleSpan G).sum_mem (fun p _=> vertex_triples p)
lemma pillar_HC (u:PlaqAxes): HC (vertex u:Curly G) 3:= markHC (Stems.Log.flame (0,u)) _
lemma dress_hc {p:Curly G}(h:HC p k)(x:Cover):HC (dress x p) k:= by apply leafy.mpr; rw [dress,Heat.Top.cut_relabel, leafy.mp h]
lemma pillar_mask (χ:Floor R)(k:ℕ): HC (mask (G:=G) q χ k) 3:= by
    apply leafy.mpr; unfold mask fireMask beadR; simp_rw [dress_fire, Finsupp.linearCombination_apply,Finsupp.sum,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_sum,map_smul,map_sum]; exact Finset.sum_congr rfl fun z _=> congr_arg _ (Finset.sum_congr rfl fun i _ => leafy.mp (dress_hc (pillar_HC i) z))
lemma roarP : HC (pillar G) 3:= IsWeightedHomogeneous.sum _ _ _ fun i _=> pillar_HC ..
lemma pillar_view : pillar G∈verse (G:=G) ⊤ 4:= Submodule.sum_mem _ (fun v (_:v∈Finset.univ)=> fire_verse (G:=G) v) -- ..
-- reference for every ℒ evaluations and supports. account ε^-4 normalized
abbrev myPage (q:ℕ+)(G:Gauge) := Page q {3} (Set.univ (α:=Tops G))
def shape (q:ℕ+): Foam G:= priceCo q (-4) (pillar G)
lemma price_cut {p:Curly G}{n:ℤ} (h:HC (V:=Hair G) p k): liftCut k (priceCo q n p)=priceCo q n p:= by ext1; rw [cut_acc]; unfold priceCo; rw [map_smul,leafy.mp h] -- bad n:P Unit
lemma shape_health (hq:1<q.val): shape q (G:=G)∈myPage q G:= by
    have hx:priceCo q (-(↑(4:ℕ):ℤ)) (pillar G) ∈ Page q Set.univ (Set.univ (α:=Tops G)):= verse_page q hq pillar_view; have he:= through q (Set.univ (α:=Tops G)) (d:=3) hx; rw [price_cut roarP] at he; exact he
end YM.PositionX.Tot
