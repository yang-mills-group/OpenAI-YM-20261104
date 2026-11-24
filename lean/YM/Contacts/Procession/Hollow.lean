import YM.Contacts.Procession.Tills
import YM.Contacts.Procession.Reel
/-!
# Formal seeded Ward preparation on the repetition scheme.

Supplies through all orders. Uses `Beam` of REAL operator on every requested period, no transport of a root transformation under a block unless scripted. `Ribbon.Motion predecessor` port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Welcome
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β ι:Type}{G:Gauge}{σ:ℝ≥0}{b s:ℝ}{m:Side}{u B i k j r n d p t:ℕ}
local notation "α†"=>Lines G m 1
variable {U Y:House α}{H V:House (Lines G m 1)}
lemma shift_again(i k:ℕ)(U:House α): shiftA i (shiftA k U)= shiftA (i+k) U:= by
   ext1 p; unfold shiftA; split_ifs<;> first| rfl| omega| congr 1 <;> omega
lemma wind_turn [Fintype α] (Y: House α)(t i d:ℕ): House.wind (shiftA t Y) (i+t) (d+t)= House.wind Y i d:= by
   funext z; unfold House.wind; rw [Nat.add_sub_add_right]; apply sum_congr rfl; intro j _; unfold House.grate shiftA; split_ifs <;> first| rfl | omega | (congr! 2 <;> omega) | (simp [parcel_nil]) -- split contract
lemma wind_gloom [Fintype α] {F:House α}(h:Snug F)(he: k<t): House.wind (shiftA t F) d k=0 := by
   funext z; refine sum_eq_zero fun i hi=>?_ ; unfold House.grate shiftA; split_ifs
   next u v=> rw [h.thin _ _ (.inr (by omega))]; exact parcel_nil ..
   all_goals first| exact parcel_nil ..| rfl
lemma wind_add [Fintype α] (U Y:House α)(i d:ℕ): House.wind (U+Y) i d= House.wind U i d + House.wind Y i d:= by
   funext x; have h (t:ℕ): House.grate (U+Y) d t x=House.grate U d t x+House.grate Y d t x:= by unfold House.grate; split<;> rename_i hv; exact parcel_add x _ _; simp
   simp_rw [Pi.add_apply,House.wind,h, sum_add_distrib]
lemma calm_zero : GuardsL (n:=m) (0:Link G m→ℝ) k:= ⟨continuous_const, analyticAt_const,fun _ _=>rfl,by simp only [Pi.zero_apply,sub_zero]; exact fun _=> Asymptotics.isBigO_zero ..⟩
lemma color_walk {F P:Link G m→ℝ}(h:GuardsL F k)(he:GuardsL P k): GuardsL (F+P) k∧ GuardsL (F-P) k:= by
   let Y(y:Link G m→ℝ)(z:Swatch G m):= y (moveField z)-y z.2; refine ⟨⟨h.cont.add he.cont,h.analytic.add he.analytic,fun _ _=>by simp [h.color,he.color],?_ ⟩,⟨h.cont.sub he.cont,h.analytic.sub he.analytic,fun _ _=>by simp [h.color,he.color],?_⟩⟩
   · change Rays k (Y _); rw [show Y (F+P)=Y F+Y P from funext (fun x=>by simp [Y]; abel)]; exact h.grade.add he.grade
   change Rays k (Y _); rw [show Y (F-P)=Y F-Y P from funext (fun x=>by simp only [Y, Pi.sub_apply];abel)]; exact h.grade.sub he.grade
lemma sealedL_shift (h:Snug H)(p:ℕ)(hL:sealedL H k): sealedL (shiftA p H) (k+p):= by
   intro i hi; by_cases hv:p ≤ i
   · generalize he:i-p=j; rw [show i=j+p from by omega,wind_turn, Nat.add_sub_add_right]; apply hL j (by omega)
   rw [wind_gloom h (by omega)]; apply calm_zero
lemma sealedL_prev (p:ℕ)(hL:sealedL (shiftA p H) (k+p)): sealedL H k := by
   intro i hi; have he:= hL (i+p) (by omega); rwa [wind_turn,Nat.add_sub_add_right] at he
lemma sealed_down_long (F:House α)(j:ℕ) : True:= trivial -- remove
lemma seal_prefix {H V:House (Lines G m 1)}(hL:sealedL H k)(he:∀ i<k,H i=V i): sealedL V k:= by
   intro i hi; apply Eq.mp _ (hL i hi); congr! 1; funext z; unfold House.wind; apply sum_congr rfl; intro j hj; have hj:=mem_range.mp hj; unfold House.grate; split; rw [he (i+j-2) (by omega)]; rfl
lemma seal_add (h:sealedL H k)(he:sealedL V k): sealedL (H+V) k:= fun i hi => wind_add H V k i|>.symm ▸ (color_walk (h i hi) (he i hi)).1
lemma seal_cancel (h:sealedL H k)(he:sealedL (H+V) k): sealedL V k:= fun i hi=> by have hh:=(color_walk (he i hi) (h i hi)).2; rwa [wind_add,add_sub_cancel_left] at hh
lemma relaxed (h: sealed H k) : sealedL H k:= fun i hi=> ⟨(h i hi).cont,(h i hi).analytic,(h i hi).color,(h i hi).grade⟩
-- Announce mark with nonnegative orders and rank <=pe, shifted into ordinary Ward screen test at charge count p+2.
structure Nation (G:Gauge)(m:Side)(p:ℕ) (H:House (Lines G m 1)): Prop where
   proper: Proper p H
   birth (k:ℕ): sealedL (shiftA (p+2) H) (k+3)
lemma Frost (h:Nation G m p H)(hk:3≤ k)(d:ℕ): sealedL (shiftA (p+2+d) H) (k+d):= by
    have hv:=sealedL_shift (tagged (k:=p+2) h.proper (by omega) (by omega:p+2>0)) d (h.birth (k-3)); rw [shift_again,Nat.sub_add_cancel hk] at hv; rwa [add_comm (p+2) d]
end YM.Contacts.Procession.Welcome
