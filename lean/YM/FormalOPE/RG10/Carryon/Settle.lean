import YM.FormalOPE.RG10.Carryon.Greeting
/-!
# Conventions with the WilsonX system. Recover exact bare funding using the
 first coefficient of the Peal diagnostic. No changes to the actual Gram
 theorems.Attaches not asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Matrix
open PertExtension MeasureTheory Topology Metric PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G:Gauge}{F:Frames G}{D:Stock F}{P:Plan F}{Y:Drivers}
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n

abbrev arrival (Z:Patience P Y) : Rack F:= fun _=> Z.Yield
lemma assessed (Z:Patience P Y) : Init (arrival Z) P.stock=arrival Z:= by
 funext d x; let E:= P.stock d; let f:= arrival Z d
 have he: E.Regular (fun v=> constantCoeff (f v)):= (funext (Z.leading (d:=d))) ▸ Z.certified.fresh d
 let L:= Matrix (Deck F d) (Deck F d) fps; let e: L:=1;
 have hv : PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n f e = f:= by
    funext v; unfold e; rw [show (1:L)=(fun i j=> if i=j then 1 else 0) from rfl]; convert! insert_one f v using 4; congr! 1
 have hh: E.position f=e:= by
    apply E.uniqueness he
    · intro i; rw [E.normalizes he]; symm; unfold TestSystem.response; rw [hv]; exact Z.ordering
    · simp
    · intro i j; unfold E e L; rw [Z.certified.normal]; by_cases hi:i=j <;> simp [Matrix.one_apply,Physical.diag,hi]
    intro i hi; refine E.Z.sub_mem (x:=fun j k=>coeff i (e j k)) (y:=fun j k=>coeff i (E.position f j k)) ?_ (E.positive_variation f i hi.ne'); change Stg (1:L) i ∈ E.Z; rw [zero_at _ hi]; exact Submodule.zero_mem _
 unfold Init TestSystem.positioned; exact ((congr_fun (congr_arg (PertExtension.Position.insert _ _ f) hh) x).trans (congr_fun hv x))
lemma doneShift (p:Warp)(h:p=Warp.still) : p.refund=p:= by subst p; apply Eq.symm; apply Warp.refund_for (h:=by simp [Warp.Hot,Warp.still]) (hz:=?_); simp only [Warp.step,Warp.still_charge]
lemma arrived (Z: Patience P Y)(hG:G.Simple): Convention (Init (arrival Z) P.stock)=Warp.still:= by rw [assessed]; exact Warp.ext (Z.calibration hG)
lemma took (Z: Patience P Y)(hG:G.Simple): mintRack (Init (arrival Z) P.stock)=arrival Z:= by funext i j; unfold mintRack; rw [doneShift _ (arrived Z hG),arrived Z hG,assessed]; simp
lemma owed (u: Rack F): coeff 1 (Convention u).x* (slope G) = coeff 1 (together F (u 6)) * (if slope G≠0 then 1 else 0) := by
 unfold Convention charged mint deviation; simp only [coeff_C_mul,map_sub,coeff_C,if_neg (by decide : ¬1= (0:ℕ)),sub_zero]; split_ifs with h
 · field_simp
 simp [not_not.mp h]
lemma taxing {u:ℕ+→ℕ→Rack F} (hG: G.Simple)(x:ℝ) : Y.Harvest (fun q n=> coeff 1 (Convention (u q n)).x) x ↔ Y.Harvest (fun q n=> coeff 1 (together F (u q n 6))) (x*slope G):= by
 have hh:= (pulse hG).ne';
 have he q n:= owed (u q n); simp only [if_pos hh,mul_one] at he
 constructor
 · intro h; unfold Drivers.Harvest; filter_upwards [h] with q h; exact (h.mul_const _).congr fun m=> he q m
 intro h; unfold Drivers.Harvest; filter_upwards [h] with q h
 have hv:= h.div_const (slope G); rw [mul_div_cancel_right₀ _ hh] at hv; apply hv.congr; intro i; rw [← he,mul_div_cancel_right₀ _ hh]

lemma gusts (Z:Patience P Y)(hG:G.Simple): Y.Harvest (fun q n=>coeff 1 (Convention (P.dressed q n)).refund.x) 1 := by
 let p(q:ℕ+)(n:ℕ):= Convention (P.dressed q n); have he : Y.Harvest (fun q n=> coeff 1 (p q n).x) (1:ℝ):= (taxing hG (u:=fun q n=> P.dressed q n) 1).2 (by rw [one_mul]; exact Z.funding)
 unfold Drivers.Harvest; filter_upwards [he] with i hv
 apply (hv.inv₀ one_ne_zero |>.mono_right (le_of_eq (by simp))).congr' (Filter.Eventually.mono ((hv.eventually (isOpen_compl_singleton.mem_nhds one_ne_zero))) ?_)
 intro j hp; let Y:=p i j; change Y.Hot at hp; change (coeff 1 Y.x)⁻¹= coeff 1 Y.refund.x
 have hh := congr_arg (fun p:Warp=>coeff 1 p.x) (Y.deposit hp)
 simp only [Warp.heats,Warp.still, coeff_one_X] at hh
 simpa only [one_div] using ((eq_div_iff hp).mpr hh).symm
end YM.FormalOPE.RG10.Carryon
