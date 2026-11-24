import YM.GradedFar.Pavilion
/-!
# Actual center response linear map for before-inverse budget

Convenience theorem on concrete N-mesh calls that keeps the SAME exterior,
including when exercising from (r,T) into (f# pulse, X). As usual, unit
center position is a shape position. Don't rewrite between gauges, y's or mounts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(P:ℝ→tower S)
variable {n m k h N N':ℕ} {e:Fin m→ℕ} (v:AppointedH140Inputs G e)
local notation "E'"=> Fin.append (Output h) e
private abbrev inPoint (m:ℕ):= Fin.castAdd m (0:Fin 1)
private def riseOne (a:Fin m→ℕ)(h:ℕ):Sec G h→ₗ[ℂ] Sec G (Fin.append (Output h) a (inPoint m)):= up (by simp [Output,inPoint])
private lemma capOne {j h:ℕ}(hj:j=h)(v:Sec G j): (⟨h,up (G:=G) (le_of_eq hj) v⟩:Sticker G)=⟨j,v⟩:= by subst h; rfl

private lemma chair (a:Sec G h) : tape (d:=Output h) (fun _=> a) v=update (tape (d:=Output h) (fun _=> 0) v) (inPoint m) (riseOne e h a):= by
 funext i
 have he(i):Fin.append (stickers (d:=Output h) (fun _=>a)) (stickers v) i=stickers (tape (d:=Output h) (fun _=>a) v) i:= by rw [tape_bill]
 have ht: ∀ i:Fin (1+m), stickers (tape (d:=Output h) (fun _=>a) v) i= stickers (update (tape (d:=Output h) (fun _=>0) v) (inPoint m) (riseOne e h a)) i := by
    intro i; by_cases hx:i=inPoint m
    · subst i; rw [← he,Fin.append_left]; unfold stickers; rw [update_self]; exact Eq.symm (capOne (by simp [Output,inPoint]) a)
    have hp:∃ j:Fin m,i=Fin.natAdd 1 j:= by
       cases i using Fin.addCases with
       | left i=> exact False.elim (hx (congrArg (Fin.castAdd m) (Subsingleton.elim _ _)))
       | right i=> exact ⟨i,rfl⟩
    unfold stickers; rw [update_of_ne hx]; obtain ⟨j,rfl⟩:= hp; change stickers (tape _ v) _ = stickers (tape _ v) _; simp only [tape_bill,Fin.append_right]
 exact eq_of_heq (Sigma.ext_iff.mp (ht i)).2
-- fixture exact impl.
def pulseRow (h:ℕ)(r s:ℝ)(t:Lattice.Site (C.side N N'))(y:Positions m)(v:AppointedH140Inputs G e) : Sec G h→ₗ[ℂ]ℂ:=
    ((assemble F P (Fin.append (fun _:Fin 1=>r) (fun _:Fin m=>s)) (Fin.append (Output h) e) N N' t (Fin.append (0:Positions 1) y)).toLinearMap (tape (d:=Output h) (fun _=>0) v) (inPoint m)).comp (riseOne e h)
lemma pulse_row (r s:ℝ)(t:Lattice.Site (C.side N N'))(y:Positions m)(u:Sec G h) : pulseRow F P h r s t y v u = recite F P r s (0:Positions 1) y t (d:=Output h) (fun _=>u) v:= by unfold recite; rw [chair]; rfl
-- validity of simultaneous exposures at same reporter (choose address from actual Schedule at any sufficiently fine mesh)
lemma rounded_append {n:ℕ}(a:ℝ)(r:ℝ)(x:Points n)(y:Points m): address a (r•forest x y)= Fin.append (address a (r•x)) (address a (r•y)):= by
 funext i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp only [Fin.append_left,Fin.append_right] <;> (unfold address; simp)
lemma rounded_origin (a:ℝ): address a (0:Points 1)=(0:Positions 1):= by unfold address; ext; simp
lemma can_call (r δ T:ℝ)(hr:0<r)(ht:0<δ): ∀ᶠ p in (again f).fuse,∀ (x:Points n)(y:Points m), let z:= address (C.S.a p.1) (r•(T•y)); let z':= address (C.S.a p.1) (r•x)
    ‖rounded C r p.1 (Fin.append z' z)-forest x (T•y)‖<δ ∧ ‖rounded C r p.1 (Fin.append (0:Positions 1) z)-forest (0:Points 1) (T•y)‖<δ := by
 filter_upwards [valid_round (C:=C) (n:=n+m) r hr δ ht,valid_round (C:=C) (n:=1+m) r hr δ ht] with p hp h x y
 dsimp only; constructor
 · rw [← rounded_append]; exact hp _
 specialize h (forest (0:Points 1) (T•y)); rw [rounded_append,smul_zero,rounded_origin] at h; exact h
end YM.Integration.GradedFar.Auth
