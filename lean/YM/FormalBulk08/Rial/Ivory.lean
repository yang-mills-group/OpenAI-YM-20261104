import YM.FormalBulk08.Rial.Gush

/-! All order top identity even on matching weights/null address
triangular factors. No assumptions on frame transformations. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {S:Finset Cover} {d:ℕ} {F: Frame G d} {I E:Type*} {j e u l r D:ℕ} {η A : ℝ}

lemma bucket (V : Finset I)(T:I→Slate G d l)(j): pocket F (∑ i∈V,T i) j=∑ i∈V,pocket F (T i) j:= by
    induction V using Finset.induction with
    | empty=> simp only [Finset.sum_empty]; exact no_buns ..
    | insert i K h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,bunch,ih]
lemma RePay (k:F.Index)(w:ℕ)(T:Finset I)(P:I→Slate G d l): (pocket F (∑ i∈T,P i) w k).re=∑ i∈T,(pocket F (P i) w k).re := by rw [bucket,Finset.sum_apply, Complex.re_sum]
variable (T: SectionData F)(H:Hol G)(o: Loc G 1) (hs:T.Sound H)(hx:Bid.pop T)(hd : d+1≤D)(x y:Letter F)
lemma sticker (hp:pet F y=pet F x): sectionY T hd x (inside F y D)=paperback T (mint F x):= by unfold sectionY inside; rw [Dawn.notch_basis];simp [hp]
lemma thinner (hp:pet F y≠pet F x): sectionY T hd x (inside F y D)=0:= by unfold sectionY inside; rw [Dawn.notch_basis,if_neg (show _ from (fun h=>hp (Subtype.ext h.symm))),zero_smul]
-- needle: sum at projected slot number b, ALL contribution can only arrive
-- e=b-a. Other orders are nil.
private lemma slant_slot (hp:pet F y=pet F x)(hx:slots F y≠slots F x+e): coeff e (echo F (sectionY T hd x) y)=0:= by
   rw [echoline]; apply Finset.sum_eq_zero; intro i hi; split
   next h => rw [sticker T hd x y hp, paperback, pinpaths T (mint _ x) _ _ (by have hz:=Finset.mem_range.mp hi; change i≠ slots F x+_;omega), hymn_vanish,chalk_void]
   rfl
include hs hx o
lemma seating_match (e:ℕ) (hu:pet F y=pet F x) (hq:slots F y=slots F x+e): coeff e (echo F (sectionY T hd x) y)=if x=y then 1 else 0:= by
   let c:=slots F y; let w:=label F y; let i:=mint F y; let Z (k:ℕ):= hymn (rancho (paste (lights T (mint F x))) k k)
   rw [echoline];
   have Hq: ∑ k ∈ Finset.range (c+1), pearlJ F (Z k) i=if x=y then 1 else 0:= by
       unfold pearlJ; rw [←RePay (l:= c)]
       change (pocket F _ w i).re=_
       have he : Tensor.coeff (hive T x) c 0=∑ k∈Finset.range (c+1), slate (Z k) d c:= banking T x o c
       rw [← he, Pose.pocket, diagonal_lifts T H hs x _ w (slotsFits F y) (F.bound i) rfl]
       rw [show (w,c)=F.grades i from rfl, ←Film.costs_only, F.coords_basis]
       split
       next h=> subst x; simp [i]
       next h=>
          have hv : i≠ mint F x:=fun e=>h (Subtype.ext (Prod.ext e.symm hu.symm))
          simp [hv]
   refine Eq.trans (Finset.sum_congr rfl (fun k hk=>?_)) Hq
   have hk:=Finset.mem_range.mp hk
   by_cases ht:slots F y - k ≤ e
   · rw [if_pos ht,sticker T hd x y hu]; unfold paperback; congr 2
     unfold dabs stencilP rancho; rw [after_one, show (F.grades (mint F x)).2+ _=k from ?_]; change Pose.slots F x+_= _; omega
   rw [if_neg ht]; unfold Z; rw [show rancho _ k k=0 from ?_, hymn_vanish, chalk_void]; rw [rancho,litLower_coeff T (mint F x) hx k _]; apply marble_zero
   change k<Pose.slots F x; omega

lemma chairs : echo F (sectionY T hd x) y= if x=y then 1 else 0:= by
    ext1 e; rcases eq_or_ne x y with he|he
    · subst y; rw [if_pos rfl,coeff_one]; cases e
      · simpa using seating_match T H o hs hx hd x x 0 rfl (Nat.add_zero _).symm
      simpa using slant_slot T hd x x (e:=_+1) rfl (by omega)
    rw [if_neg he,map_zero]; by_cases hy:pet F y=pet F x
    · by_cases hp:slots F y=slots F x+e
      · rw [seating_match T H o hs hx hd x y _ hy hp,if_neg he]
      exact slant_slot T hd x y hy hp
    rw [echoline]; apply Finset.sum_eq_zero; intro i hi; split
    next hc=> rw [thinner T hd x y hy]; exact chalk_void ..
    rfl

end YM.FormalBulk08.Rial
