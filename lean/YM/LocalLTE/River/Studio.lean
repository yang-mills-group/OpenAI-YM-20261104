import YM.LocalLTE.River.Painter
/-! Passing capital at actual union supports. `atoms` need *per-atom*
prices awarded IN the canonical joint frame. Here we use no Born-
Haar measure extension. Support costs incur after projecting. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals
variable {L:Support n}
section emit
variable {U:ℕ→Support n} {W:ℕ→ Config G n→ℂ}
variable (hI:∀ i,0∈ U i)(h: Local.Readable A D p n y) (hz: D.footprint (0:Site n)⊆ neighbors ℓ 0)
local notation "P'"=> Vinca.emit D A U 0 p.threshold 0 W
local notation "K"=> Push.Local.factor A D p.supportExponent y
include h hI hz
lemma minted (hp:Patched p 0 U W v) (X:Grove (0:Site n)) (hv:j ≤ ℓ)(hw:∀ i,W i≠0 →(∀ b:Bool, Replicated X j k (m+1) (Port.scaleQ b ∘ W i))∧ U i ⊆ neighbors ℓ 0) : Patrons D k ℓ m p (Vinca.emit D A U 0 p.threshold 0 W) (K*v):=by
    obtain ⟨c,hV,hf⟩:= hp.permit
    let Y i:=p.mass (Push.Local.joint D (0:Site n) (U i)); let a:= Local.atomPrice A F y; have hy:1≤a:= Local.atomPrice_ge_one _ _ h.nonneg
    have hK:1≤K:=Dilation.factorLarge h
    have he : SumBudget (fun i=> Y i (a*c i)) (K*v):= Local.sumBudget_mono (Local.sumBudget_mul_left hV (zero_le_one.trans hK)) (fun i=> mul_nonneg (Real.exp_pos _).le (mul_nonneg (zero_le_one.trans hy) (hf i|>.2.1))) (fun i=> (show Y i (a*c i) ≤ Push.Local.reservedMass p (Push.Local.joint D 0 (U i)) (a*c i) from mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (mul_nonneg (zero_le_one.trans hy) (hf i|>.2.1))).trans (Local.price_join D A 0 (hI i) h.sound h.nonneg (hf i|>.2.1))) le_rfl
    refine ⟨?_, ⟨(fun i=> a*c i), he, ?_⟩,rfl⟩
    · have hk:=(Vinca.painted D A U (0:Site n) h hI hp).1
      rw [show (P').x= (0+_) from rfl,zero_add]; exact (Size.bound F hk.2.1).trans hk.2.2
    intro i; let Z:= U i; let f:=W i; have hc := (Local.charge_atom (0:Site n) h ((hf i).1) ((hf i).2)).1
    refine ⟨hc,fun hP=>?_⟩; have hf':W i ≠ 0:=by intro hz; apply hP; unfold Vinca.emit Local.residual; simp only [hz]; rw [show Push.Local.weighted A F 0 (U i) p.threshold (0:Config G n→ℂ)=0 from ?_,map_zero,sub_zero]; simp [Push.Local.weighted] -- rg
    let ζ:= Local.weighted A F (0:Site n) Z p.threshold f
    obtain ⟨hq,hz'⟩:= hw i hf'; have hu:= (hf i).2
    have hx: Push.Local.readPrice A F ≤ a:=by unfold a atomPrice; have h:= h.nonneg; have hπ:=readPrice_pos A F; nlinarith only [h,hπ]
    have hV' : F.coeffSize (-ζ) ≤ a * c i:=by
       rw [show -ζ=(-1:ℂ) • ζ from (neg_one_smul _ _).symm, Size.smul,norm_neg,norm_one,one_mul]; exact (Local.weighted_bound A F 0 ((hf i).1) h.order h.power hu).trans (mul_le_mul_of_nonneg_right hx hu.1)
    refine ⟨Finset.union_subset hz' hz, W i,regular_larger ((hf i).1) Finset.subset_union_left, bound_larger (bound_weaken hu (le_mul_of_one_le_left hu.1 hy)) Finset.subset_union_left,⟨-ζ,hV',?_⟩,j,hv,X,hq⟩
    change f- presented D 0 p.threshold ζ=f+_; rw [map_neg,sub_eq_add_neg]

end emit
-- Ordered price helper.
section cap
variable {U:ℕ→Support n} {W:ℕ→ Config G n→ℂ}
variable (hq: ∀ i,0∈ U i)
-- For Dilation.out unused,P'=0 on ordinary support
lemma saplingZero (L:Support n): Canvas D k ℓ m p L 0 0:= Canvas.quiet le_rfl
lemma patronC {P:Coefficient F n} (h:F.coeffSize P.x ≤ y)(hf:P.forced=0)(he:P.regular=0): Patrons D k ℓ m p P y:=by
    refine ⟨h, ⟨(fun _ =>0), ?_, fun i=> by rw [he]; exact Canvas.quiet le_rfl⟩, hf⟩; have hp:= (Work.G08.size_nonneg ..).trans h
    simp only [BudgetPoint.mass,mul_zero]; exact Local.sumBudget_zero hp
end cap
end YM.LocalLTE.River
