import YM.FormalOPE.RG10.Carryon.Portfolio
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G : Gauge} {F : Frames G} {d : ℕ}
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n

/-- A single-position (Stock frames solved earlier) triangular change of parameter.
Cannot claim attached unit slopes without `Hot`. -/
abbrev Wind := Warp
def charged (a:(V 6)→fps) : Warp:= ⟨ mint F a,mint_zero ..⟩
def Warms (a:(V 6)→fps) := coeff 1 (mint F a)≠0

namespace Warp
variable (p q: Warp)

abbrev Hot := coeff 1 p.x ≠ 0
abbrev step : Warp:= ⟨p.charge q.x,(p.smoothed _).trans q.atOrigin⟩
def still : Warp := ⟨PowerSeries.X,constantCoeff_X⟩
@[simp] lemma still_charge (x:fps) : still.charge x=x := by rw [turning]; exact X_subst x

lemma take (p q : Warp)(φ: fps) : (p.step q).charge φ=p.charge (q.charge φ) := by
  simp_rw [step,turning]; exact (subst_comp_subst_apply (good q.x q.atOrigin) (good p.x p.atOrigin) _).symm
@[ext] lemma ext {p q : Warp}(h : p.x=q.x): p=q:= by cases p; cases q; congr
lemma heats (a:fps) : coeff 1 (p.charge a)= coeff 1 a * coeff 1 p.x := by
 rw [turning, AlignSeries.subst_finite p.atOrigin]; rw [Finset.sum_range_succ]; simp
lemma flames : (p.step q).Hot ↔ p.Hot ∧ q.Hot := by rw [Hot,step, heats]; simp [and_comm,Hot]

abbrev refund : Warp:= ⟨ Triangle.inverseScale p.x,inverse_zero _⟩
lemma cash (h:p.Hot) : p.refund.step p = still := by
 ext : 1;
 dsimp only [still,step,refund]; rw [turning]; change subst (inverseScale p.x) p.x=PowerSeries.X; rw [inverseScale,dif_pos (isUnit_iff_ne_zero.mpr h : IsUnit (coeff 1 p.x))]; exact p.x.subst_substInvOfIsUnit_right p.atOrigin _
lemma deposit (h:p.Hot) : p.step p.refund= still := by
 apply Warp.ext;
 dsimp only [still,step,refund]; rw [turning,inverseScale,dif_pos (isUnit_iff_ne_zero.mpr h : IsUnit (coeff 1 p.x))]; exact p.x.subst_substInvOfIsUnit_left p.atOrigin _
lemma refund_worthy : p.refund.Hot:= by
 by_cases h:p.Hot
 · apply ((flames p.refund p).mp _).left; rw [cash p h]; simp [Hot,still]
 change coeff 1 (inverseScale p.x) ≠ 0; rw [inverseScale, dif_neg (show ¬ IsUnit (coeff 1 p.x) from (fun hn => h (isUnit_iff_ne_zero.mp hn)))]; simp
lemma refund_for (h:p.Hot)(hz:q.step p=still) : q=p.refund:= by
 have hh:= show q.step (p.step p.refund)= (q.step p).step p.refund from Warp.ext (take q p _).symm
 rw [deposit _ h,hz] at hh
 apply Warp.ext; apply Eq.trans _ ((congr_arg Warp.x hh).trans (still_charge _)); change q.x=q.charge PowerSeries.X; rw [turning,subst_X (good q.x q.atOrigin)]

variable (a : Mark (Deck F 6) PertExtension.Physical.Profile.n → fps)
lemma trade : charged (p.charge ∘ a)= p.step (charged a) := by
 apply Warp.ext
 have he: together F (p.charge ∘ a)= p.charge (together F a):= together_maps F (p.charge : fps→+*fps) (base p) a
 unfold charged step mint; simp only [he,deviation,map_sub,map_mul,p.smoothed,base]
lemma trading (h:(charged a).Hot)(hp:p.Hot)(φ:fps) : Xaction F (p.charge ∘ a) (p.charge φ)= Xaction F a φ := by
 let t:=charged a; let k:= (charged (p.charge ∘ a)); have hk : k=p.step t:= trade ..
 have hf:= k.cash (by rw [hk]; exact (flames ..).mpr ⟨hp,h⟩)
 have hh : k.refund.step (p.step t)= (k.refund.step p).step t:= Warp.ext (take k.refund p _).symm
 have hm : k.refund.step p=t.refund:= refund_for t _ h (hh.symm.trans (hk ▸ hf))
 change k.refund.charge _=t.refund.charge _; rw [← take,hm]
end Warp
end YM.FormalOPE.RG10.Carryon
