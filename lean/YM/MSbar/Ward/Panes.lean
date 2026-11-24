import YM.MSbar.Ward.Grid
/-! From film to epoch. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open Shield
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{c d e:Bit}{X:Pulse W}{F G H:ListV C}{k n i j:ℕ}{z:ℂ}
abbrev Gems (W: Edition C)(d:Bit)(F:Film C) := ∀ v z, Live W d (F v z)
def pane (W:Edition C)(d:Bit)(F:ListV C)(z:ℂ): Epoch.Whole (Desk W d) := fun k n=> shutter W d (F k n) z
lemma trip {A:Mono W 0 d}{F:ℕ→Film C}: Gems W d (tripped A F k):= by cases k; exact fun _ _=> Live.zero; exact fun _ _=> delay_live
lemma reach {A:Poly W 0 0 d}: Gems W d (seek A F G k n):= by intro i z; simp_rw [seek, Finset.sum_apply];exact Live.sum _ fun x _=> Live.sum _ fun y _=> make_live
namespace Gems
variable {F G H:Film C}
lemma add (h:Gems W d F)(hg:Gems W d G):Gems W d (F+G):= fun i z=> Live.add (h i z) (hg i z)
lemma scale (h:Gems W d F)(c:ℂ): Gems W d (c•F):= fun i z=>Live.scale c (h i z)
lemma sub (h:Gems W d F)(hg:Gems W d G): Gems W d (F-G):= fun i z=>Live.sub (h i z) (hg i z)
lemma plus (h:Gems W d F)(hg:Gems W d G): shutter W d (F+G) z= shutter W d F z+shutter W d G z:=funext fun v=>add' (h v z) (hg v z)
lemma take (h:Gems W d F)(hg:Gems W d G): shutter W d (F-G) z= shutter W d F z-shutter W d G z:=funext fun v=>sub' (h v z) (hg v z)
lemma times (h:Gems W d F)(c:ℂ): shutter W d (c•F) z=c•shutter W d F z:=funext fun v=>scale' (h v z) c
end Gems
lemma empty (z:ℂ)(W:Edition C): shutter W d 0 z=0:=funext fun _=> nil
lemma scored (X:Pulse W): Gems W 0 (Score X F k n):= Gems.add trip (Gems.scale reach _)
lemma grid1 (A:Mono W 0 d): shutter W d (tripped A (F k) n) z= act (sea (sea (A z))) (pane W 0 F z) k n:=by cases n with | zero=>exact empty z W | succ n=> exact shutter_delay A
lemma grid2 (A:Poly W 0 0 d): shutter W d (seek A F G k n) z= knot (knot (knot (A z))) (pane W 0 F z) (pane W 0 G z) k n:=by
   funext v; simp_rw [knotted, Finset.sum_apply]; unfold shutter seek; simp_rw [Finset.sum_apply]; rw [sum' (fun i hi=> Live.sum _ fun x hx=> make_live)]; refine Finset.sum_congr rfl (fun i hi=> ?_); rw [sum' (fun i hi=> make_live)]; rw [knotted,Finset.sum_apply]; exact Finset.sum_congr rfl fun j hj=> congr_fun (shutter_make _) _
variable (A:Shield X)
lemma generator (F: ListV C): shutter W 0 (Score X F k n) z= Calculus.current (Epoch.grow (propagate (engine A z) true)) (pane W 0 F z) k n:=by
    unfold Score; rw [Gems.plus trip (Gems.scale reach _),Gems.times reach,grid1,grid2]; unfold Calculus.current; simp only [Pi.sub_apply,Pi.smul_apply,sub_eq_add_neg]; let v:= (Epoch.grow (propagate (engine A z) true)).bond (pane W 0 F z) (pane W 0 F z) k n; refine congr_arg (fun v:Desk W 0 => (Epoch.grow (propagate (engine A z) true)).white (pane W 0 F z) k n+v) ?_; exact neg_smul ((2:ℂ)⁻¹) v

namespace Shield
def flux (F:ListV C): ListV C:= fun k n=> Play.spin A.R0 (F k n)+ (2:ℂ)⁻¹ • seek A.B0 F F k n - tripped A.D0 (F k) n
lemma acts (F:ListV C): Gems W 1 (flux A F k n) := Gems.sub (Gems.add (fun i z=> spin_live) (Gems.scale reach _)) trip
lemma audit (F:ListV C)(z:ℂ): pane W 1 (flux A F) z= Calculus.anomaly (Epoch.grow (propagate (engine A z) true)) (pane W 0 F z):= by
    funext k n; change shutter W 1 _ z=_; unfold flux; rw [Gems.take (Gems.add (fun i z=> spin_live) (Gems.scale reach _)) trip,Gems.plus (fun i z=> spin_live) (Gems.scale reach _), Gems.times reach, grid2, grid1, shutter_spin]; rfl
end Shield
end YM.MSbar.Play.Produce
