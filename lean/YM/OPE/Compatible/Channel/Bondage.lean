import YM.OPE.Compatible.Channel.Hearth
/-!
# Per-block power counting exact transfer of graded moment disappearances
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m j k:ℕ}{L c f:Side}{η U v:ℝ}
namespace Script
open Page
variable (W:Type*)[Fintype W] [DecidableEq W] (hv:0<v) (hj:4 ≤ j)(hk:4 ≤ k)
abbrev opal (P:Flight j k)(x:ℝ)(p: Script (Palette W) r):=countermove (chrome W (linesOf P x)) 0 p
abbrev mat (P:Flight j k)(x:ℝ)(p: Script (Palette W) r):= payVolume (chrome W (linesOf P x)) p
include hv hj hk
lemma opus (ha:n ≤ j-2)(he:n ≤ m)(r:ℕ):∃ B:ℝ,0≤ B∧∀ (P:Flight j k) z (p:Script (Palette W) r), soot m p z→Bells p n→ soot m (opal W P v p) (B/(P.L.val:ℝ)^(r+n)*z):=by
    obtain ⟨C,hC,H⟩:= stamp_local hv hk hj ha he r
    let x:ℝ:= Fintype.card (Ink (Palette W) r); refine ⟨x*x*C, ?_,fun P z p h hp=>?_⟩
    · have ht:0≤x:=Nat.cast_nonneg _; positivity
    let k (i j:Ink (Palette W) r) := banner P (ringList i) (ringList j) v (sliceP p i); have hb (i j:Ink (Palette W) r):= H P (ringList i) (ringList j) z (sliceP p i) (slices h _) (hp _)
    let u:= C/(P.L.val:ℝ)^(r+n)*z; have hu:0 ≤ u:= mul_nonneg (div_nonneg hC (by positivity)) h.coins
    have ht(j):Sack (poise m) (sliceP (opal W P v p) j) (x*u):=by
       unfold opal; rw [pay_div _ (stored P v hv hk) h]; change Sack _ (∑ i:Ink (Palette W) r,if ringTone i=ringTone j then k i j else 0) _; apply (Sack.finGather (B:=fun _=> u) _ _ ?_ (fun x=> zero_le_one.trans (poise_one m x))).tips; swap
       · intro i _; split; exact hb _ _; exact Sack.zero hu _
       rw [sum_const,nsmul_eq_mul]; rfl
    apply (layered _ ht).tips; change x*(x*u) ≤ _; exact le_of_eq (by unfold u; ring)
lemma volMat (ha:n ≤ j-2)(he:n ≤ m) (r:ℕ):∃ B:ℝ,0≤ B∧∀ (P:Flight j k) z (p:Script (Palette W) (r+1)), soot m p z→Poll p n→ pinned p→ soot m (mat W P v p) (B*(P.L.val:ℝ)^4/(P.L.val:ℝ)^(r+1+n)*z):=by
    obtain ⟨C,hC,H⟩:= stamp_globe hv hk hj ha he r
    let x:ℝ:= Fintype.card (Ink (Palette W) (r+1)); refine ⟨x*x*C, ?_,fun P z p h hp hx=>?_⟩
    · have ht:0≤x:=Nat.cast_nonneg _; positivity
    let n' := (r+1); let k (i j:Ink (Palette W) (r+1)) := pilgrim P (ringList i) (ringList j) v (crop p i); have hb (i j:Ink (Palette W) (r+1)):= H P (ringList i) (ringList j) z (crop p i) (crops h _) (hp _)
    let u:= C*(P.L.val:ℝ)^4/(P.L.val:ℝ)^(r+1+n)*z; have hu:0 ≤ u:= mul_nonneg (div_nonneg (by positivity) (by positivity)) h.coins
    have ht(j):Sack (poise m) (sliceP (mat W P v p) j) (x*u):=by
       unfold mat; rw [lifters hx h hk hv]; change Sack _ (∑ i:Ink _ n',upland (if ringTone i=ringTone j then k i j else 0)) _; apply (Sack.finGather (B:=fun _=> u) _ _ ?_ (fun x=> zero_le_one.trans (poise_one m x))).tips; swap
       · intro i _; split; exact upland_bill (hb _ _); exact upland_bill (Sack.zero hu _)
       rw [sum_const,nsmul_eq_mul]; rfl
    apply (layered _ ht).tips; change x*(x*u)≤_; exact le_of_eq (by unfold u; ring)
end Script
end YM.OPE.Flume
