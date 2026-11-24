import YM.OPE.Compatible.Channel.Bondage
/-!
# First action in P flags gets graded stipends -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m j k:ℕ}{L c f:Side}{P:Flight j k}{η U v:ℝ}
namespace Script
open Page
variable {W:Type*}[Fintype W] [DecidableEq W]
local notation "L"=>((P.L.val:ℝ)⁻¹)
omit [Fintype W] [DecidableEq W] in
private lemma ink_eq {u v:Ink (Palette W) r} (h:ringTone u=ringTone v)(hx:ringList u=ringList v): u=v:=funext fun i=>Prod.ext (congr_fun hx i) (congr_fun h i)
lemma opus_well (p:Script (Palette W) r)(hp:soot m p U)(hv:0<v)(hk:4 ≤ k)(b:Ink (Palette W) r)(l:List (Keys r))(h:p.Bells l.length)(hg:l.length≤m)(hx:l.length<j):
    well (sliceP (opal W P v p) b) (tasting l)= L^(r+l.length) *well (sliceP p b) (tasting l):=by
    unfold opal; rw [pay_div _ (stored P _ hv hk) hp]; let f i:= banner P (ringList i) (ringList b) v (sliceP p i); let g i:= if ringTone i=ringTone b then f i else 0
    have ht(i):well (f i) (tasting l)=(if ringList i=ringList b then L^(r+l.length) else 0)* well (sliceP p i) (tasting l):= stock_stamp (slices hp i) hk hv _ _ _ (fun _=> by simp [size]) l hx hg (h _)
    have hp i : ∃ z,Sack (poise m) (g i) z:=by
       obtain ⟨A,-,hA⟩:= stamp_local (n:=0) (m:=m) hv hk P.legal (Nat.zero_le _) (Nat.zero_le _) r
       unfold g; split; next he=> exact ⟨_,hA P _ _ _ _ (slices hp _) (by intro y hy; simp at hy)⟩
       next he=> exact ⟨0,Sack.zero le_rfl _⟩
    change well (∑ i,g i) (tasting l)=_
    rw [wellsSet _ _ _ (flavor_part l m hg) (fun i _=> hp i), Finset.sum_eq_single b]; swap; intro i _ hi; unfold g; split_ifs with h
    · rw [ht,if_neg (fun hh=>hi (ink_eq h hh)),zero_mul]
    swap; unfold g; rw [if_pos rfl,ht,if_pos rfl]
    swap; · simp
    simp [well]
lemma globe_well (p:Script (Palette W) (r+1))(hp:soot m p U)(hv:0<v)(hk:4 ≤ k)(b:Ink (Palette W) (r+1))(l:List (Keys r))(h:p.Poll l.length)(hg:l.length≤m)(he:p.pinned)(hx:l.length<j): well (crop (mat W P v p) b) (tasting l)= (P.L.val:ℝ)^4 * L^(r+1+l.length) *well (crop p b) (tasting l):=by
    let f i := pilgrim P (ringList i) (ringList b) v (crop p i); let g i:= if ringTone i=ringTone b then f i else 0
    have ht i: well (f i) (tasting l)=(P.L.val:ℝ)^4 * (if ringList i=ringList b then L^(r+1+l.length) else 0)* well (crop p i) (tasting l):= pilgrim_well _ (crops hp i) l hg hx hv hk _ _ (h _)
    have hP i : ∃ z,Sack (poise m) (g i) z:=by
       obtain ⟨A,-,hA⟩:= stamp_globe (n:=0) (m:=m) hv hk P.legal (Nat.zero_le _) (Nat.zero_le _) r
       unfold g; split; next he=> exact ⟨_,hA P _ _ _ _ (crops hp _) (by intro y hy; simp at hy)⟩
       next he=> exact ⟨0,Sack.zero le_rfl _⟩
    have heq : crop (mat W P v p) b=∑ i,g i:= funext fun i=>by
        unfold mat crop; rw [lifters he hp hk hv]; change (∑ i,upland (g i)) (wreath r (0,i))=_; rw [← upland_sum,upland,header,flattenZ,if_pos rfl]
    rw [heq,wellsSet _ _ _ (flavor_part l m hg) (fun i _=> hP i), Finset.sum_eq_single b]
    · unfold g; rw [if_pos rfl,ht,if_pos rfl]
    · intro i _ hi; unfold g; split
      next h=> rw [ht,if_neg (fun hh=>hi (ink_eq h hh)),mul_zero,zero_mul]
      next h=> simp [well]
    simp
end Script
end YM.OPE.Flume
