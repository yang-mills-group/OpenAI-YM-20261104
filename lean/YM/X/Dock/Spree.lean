import YM.X.Dock.Slant
/-!
# limiting amplitude of FB Fpv. do not cast units. Distribution derivative of energy gradient spin line determined under unexceptional spacing plots. ∗single-line P∆∗.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {m k d:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
abbrev Search (x y z:E4)(r:ℝ): Prop:= r<‖x-y‖∧r<‖y-z‖∧r<‖z-x‖
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
variable (hq:1<q.val)(χ:Floor R)(hr:R<r)
-- explicit
structure PS (q:ℕ+)(i:Axis)(A:Scaff)(p p':E4→ℝ):Prop where
  h:A∈air 1 -- redundant
  see: Atlas q 1 A p
  diff: Atlas q 2 (ds i A) p'
variable (X Y Z:Fielding.Walk)(x y z:E4)(i:Axis)(hX:plot q X x)(hY:plot q Y y)(hZ:plot q Z z)(H:Search x y z r) (P M N:Scaff)(p p' f f' g g':E4→ℝ)(A:PS q i P p p')(B:PS q i M f f')(C:PS q i N g g')
local notation "ΔP"=> run q Z 2 (ds i P)
local notation "F"=> run q X 1 M
local notation "K"=> run q Y 1 N
def lateral (q:ℕ+)(x y z:Fielding.Walk)(i:Axis)(P M N:Scaff)(k:ℕ):ℝ:= galley (epsilon q k) ((run q z 2 (ds i P)*(run q x 1 M* run q y 1 N)) k)
abbrev restored (χ:Floor R)(x y z a:E4):ℝ:= Rest χ Finset.univ (![x,y,z]:Fin 3→E4) a
abbrev billF (x y z:E4)(p' f g:E4→ℝ)(a:E4):ℝ:= (p' (z-a))*(f (x-a)*g (y-a))
def Scout (χ:Floor R)(x y z:E4)(p' f g:E4→ℝ)(a:E4):= restored χ x y z a*billF x y z p' f g a
def Hatch (χ:Floor R)(x y z w:E4)(p' f g:E4→ℝ)(a:E4):= χ.s a * billF x y z p' f g (w+a)
def Ship (χ:Floor R)(x y z:E4)(i:Axis)(p f g:E4→ℝ)(a:E4):ℝ := -Maxwell.grad i χ.s a*(p (z-(z+a))*(f (x-(z+a))*g (y-(z+a))))
def Hips (χ:Floor R)(x y z:E4)(p f f' g g':E4→ℝ)(a:E4):ℝ:= χ.s a*(p (z-(z+a))*( f (x-(z+a))*g' (y-(z+a))+f' (x-(z+a))*g (y-(z+a))))
def Armor (χ:Floor R)(x y z:E4)(i:Axis)(p p' f f' g g':E4→ℝ):Prop:= Integrable (Scout χ x y z p' f g)∧ Integrable (Hatch χ x y z x p' f g) ∧ Integrable (Hatch χ x y z y p' f g) ∧ Integrable (Ship χ x y z i p f g) ∧ Integrable (Hips χ x y z p f f' g g')
def Bolt (χ:Floor R)(x y z:E4)(i:Axis)(p p' f f' g g':E4→ℝ):ℝ:= (∫ a:E4,Scout χ x y z p' f g a) + (∫ a:E4, Hatch χ x y z x p' f g a)+(∫ a:E4,Hatch χ x y z y p' f g a)+((∫ a:E4, Ship χ x y z i p f g a)-(∫ a:E4,Hips χ x y z p f f' g g' a))
local notation "Ξ"=> (ΔP*(F*K))
local notation "Ψ"=> Scout χ x y z p' f g
local notation "B₀"=>Hatch χ x y z x p' f g
local notation "B₁"=>Hatch χ x y z y p' f g
local notation "B₂"=>Ship χ x y z i p f g
local notation "B₃"=> Hips χ x y z p f f' g g'
lemma pin_mul (w:Fielding.Walk)(U V:Rhyme q):pin q w (U*V)= pin q w U*pin q w V:= rfl -- omit included
local notation "maskX" W:arg k:arg=> (tipMask χ q W*Ξ) k
local notation "ℙ"=>Geom.head X Y Z
local notation "𝚂"=> ![x,y,z]
local notation "Qv"=> Quiet q (Finset.univ (α:=Fin 3)) ℙ χ
include hq hr hX hY hZ H A B C
lemma port_price : Integrable B₂∧ Integrable B₃∧ Tendsto (fun k=>galley (ε k) (maskX Z k)) L (𝓝 ((∫ a:E4,B₂ a)-(∫ a:E4,B₃ a)) ) := by
    let U:=run q Z 1 P; let a'(φ:E4→ℝ)(x w:E4):= φ (x-(z+w)); let a:= pin q Z U; let b:=pin q Z F; let c:=pin q Z K;
    have hu:R≥0:=χ.positive.le; have hw:r≥0:=hu.trans hr.le; have hb:=elseF hq X B.see Z hX hZ hw (norm_sub_rev z x ▸ H.2.2); have hc:=elseF hq Y C.see Z hY hZ hw H.2.1; have hd := elseF hq X B.diff Z hX hZ hw (norm_sub_rev z x ▸ H.2.2); have he:= elseF hq Y C.diff Z hY hZ hw H.2.1; rw [prospect_eq _ _ _ _] at he hd -- fix
    have hbc : Focus q R 0 (westOf i (b*c)) (fun w:E4=> a' f x w*a' g y w):= west hq hu hr i (hb.mix hc); have hθ: Focus q R 0 (westOf i (prospect i q (b*c))) (fun w:E4=> a' f x w*a' g' y w+a' f' x w*a' g y w):= by rw [twice]; exact (((west hq hu hr i hb).mix (west hq hu hr i he)).plus ((west hq hu hr i hd).mix (hc.lower hr.le)))
    obtain ⟨ht₁,ht₂,ht⟩:= range_focus hq χ i (own hq Z A.see hZ hu) hbc hθ; refine ⟨ht₁,ht₂,ht.congr' ?_⟩; filter_upwards [mask_global q χ hq] with k hk; rw [scatter χ _ hk,pin_mul,pin_mul,prospect_eq]
lemma land_x : Integrable B₀∧ Tendsto (fun k=>galley (ε k) (maskX X k)) L (𝓝 (∫ a:E4,B₀ a)):= by
    have hu:R≥0:= χ.positive.le; have hb:=own hq X B.see hX hu; have hc:=elseF hq Y C.see X hY hX hu (hr.trans (norm_sub_rev x y ▸ H.1)); have hh:=elseF hq Z A.diff X hZ hX hu (hr.trans H.2.2); obtain ⟨he,ht⟩:=magnify_mask hq χ (hh.mix (hb.mix hc)); refine ⟨he,ht.congr' ?_⟩; filter_upwards [mask_global q χ hq] with k hk; rw [scatter χ _ hk,pin_mul,pin_mul]
lemma land_y : Integrable B₁∧ Tendsto (fun k=>galley (ε k) (maskX Y k)) L (𝓝 (∫ a:E4,B₁ a)):= by
    have hu:R≥0:= χ.positive.le; have hb:=elseF hq X B.see Y hX hY hu (hr.trans H.1); have hc:=own hq Y C.see hY hu; have hh:=elseF hq Z A.diff Y hZ hY hu (hr.trans (norm_sub_rev y z ▸ H.2.1)); obtain ⟨he,ht⟩:=magnify_mask hq χ (hh.mix (hb.mix hc)); refine ⟨he,ht.congr' ?_⟩; filter_upwards [mask_global q χ hq] with k hk; rw [scatter χ _ hk,pin_mul,pin_mul]
omit hq hr hX hY hZ H A B C in
lemma castVM (U V:Rhyme q): castV (U*V)= castV U*castV V:= by ext1 ⟨z,x⟩; simp [castV]
lemma land_in : Integrable Ψ∧ Tendsto (fun k=> galley (ε k) (Qv k*(Ξ k))) L (𝓝 (∫ a:E4, Ψ a)):= by
    let S:=Finset.univ (α:=Fin 3); have hp(i:Fin 3)(_ : i∈S):plot q (ℙ i) (𝚂 i):=by fin_cases i <;> first | exact hX| exact hY| exact hZ
    have hw:Apart S 𝚂 R:= by
        intro a _ b _ hp; have hg:=hr.trans H.1; have hh:=hr.trans H.2.1; have he:= hr.trans H.2.2; have hs:= norm_sub_rev y x; have hv:=norm_sub_rev z y; have hi:=norm_sub_rev x z; fin_cases a<;>fin_cases b<;>simp_all
    have hi(j:Fin 3){k:ℕ}{A:Scaff}(h:A∈air k): Isle q S ℙ 𝚂 χ 2 (castV (run q (ℙ j) k A)):= Isle.iota _ (by omega) (barometer hq S ℙ 𝚂 χ hw hp (Finset.mem_univ j) h)
    refine horizon S ℙ 𝚂 hp hw χ hq Ξ (billF x y z p' f g) ?_ ?_; swap; · intro a he z hz; refine (A.diff.edge hZ hz (fun h=>he ⟨2, Finset.mem_univ _,h⟩)).mul ((B.see.edge hX hz (fun h=>he ⟨0, Finset.mem_univ _,h⟩)).mul (C.see.edge hY hz (fun h=>he ⟨1, Finset.mem_univ _,h⟩)))
    rw [castVM,castVM]; exact (hi 2 A.diff.mark).mul ((hi 0 B.h).mul (hi 1 C.h))
lemma goes_price : Armor χ x y z i p p' f f' g g'∧ Tendsto (lateral q X Y Z i P M N) L (𝓝 (Bolt χ x y z i p p' f f' g g')):= by
    obtain ⟨ht₁,ht₂,ht⟩:=port_price hq χ hr X Y Z x y z i hX hY hZ H P M N p p' f f' g g' A B C; obtain ⟨he,hh⟩:=land_x hq χ hr X Y Z x y z i hX hY hZ H P M N p p' f f' g g' A B C; obtain ⟨hf,h⟩:=land_y hq χ hr X Y Z x y z i hX hY hZ H P M N p p' f f' g g' A B C; obtain ⟨hv,hW⟩:=land_in hq χ hr X Y Z x y z i hX hY hZ H P M N p p' f f' g g' A B C; refine ⟨⟨hv,he,hf,ht₁,ht₂⟩,(((hW.add hh).add h).add ht).congr fun k=> ?_⟩
    change galley _ _ + galley _ _ + galley _ _+ galley _ _= _; unfold galley lateral; rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; unfold galley; apply congr_arg; refine Finset.sum_congr rfl fun z _=>?_ ; unfold Quiet tipMask transit; -- compare.sum
    simp only [Pi.mul_apply]; rw [Fin.sum_univ_succ, Fin.sum_univ_succ,Fin.sum_univ_one]; simp [Geom.head]; ring
end YM.PositionX.Chir.Dock
