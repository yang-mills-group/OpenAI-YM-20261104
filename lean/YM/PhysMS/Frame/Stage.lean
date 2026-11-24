import YM.PhysMS.Frame.Atlas
import YM.TraceExtension.Sundial.Eve

/-! One fixed X position meter *extending through all finite horizons* with
all-length leading comparison from the physical multi-arity program. Keep the
finite cap four calibration and angle test exactly. Diagonalization over
increasing demands (at same real length; not merely nearby mesh), adapted
from `Pilot.glides,glenned`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {Y:Ultrafilter (ℕ×ℕ)} (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)
  {Z:Terrace.Arch C} (hZ:Bliss F Y Z H)
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d

structure Staff (r:ℝ)(P:tower S)(m:ℕ) : Prop where
   angle : AtAngle (𝓛:=Y) (H:=H) F h r (P 4)
   spins (d:Fin (m+1)) : obedient F H P d
   rises (e:Fin (m+1)) (d:Fin (e.val+1)) : ∀ v, P e ((K).rise (Nat.le_of_lt_succ d.isLt) v)=F.sector.derivatives.rise (Nat.le_of_lt_succ d.isLt) (P d v)
   checks (n:Fin (m+1))(d:Fin n→Fin (m+1))(v:∀ i,PegC C (d i))(j:Fin (m+1)) :
       ∀ x∈Scaling.window (sizeHint m) n, ‖iteratedFDeriv ℝ j (measured F none P (fun i=> PoleC C (d i) (v i)) r) x-
          iteratedFDeriv ℝ j (WickGoal (fun i=> PoleC C (d i) (v i))) x‖ ≤ costHint m
include hZ
lemma on_crew (m:ℕ): ∀ᶠ r in trail, ∃ P:tower S, ∀ j ≤ m, Staff (Y:=Y) h F H r P j:=by
   by_contra hd; obtain ⟨s,hs,hS⟩:= contradictionTrail _ hd
   obtain ⟨v,hv,X,hX,V,hB⟩:= hZ.picks s (hs.mono_right nhdsWithin_le_nhds) (fun i=> (hS i).1)
   obtain ⟨A,hA,hT,hα,h₁⟩:= survey h F H X hB
   have he (m:ℕ): ∀ᶠ i in atTop, Staff (Y:=Y) h F H (X.r i) (A i) m:=by
      have he'(n:Fin (m+1))(d:Fin n→Fin (m+1))(w:∀ i,PegC C (d i))(j: Fin (m+1)):= Metric.tendstoUniformlyOn_iff.mp (path_lead F H X hB hA n _ (fun i=> PoleC C (d i) (w i)) j (Scaling.window (sizeHint m) n) (window_closed ..) (fun x hx=>spaced_conf (cost_pos _) hx.1)) _ (cost_pos m)
      filter_upwards [hT,eventually_all.mpr (fun i:Fin (m+1)=>hα i), eventually_all.mpr (fun e:Fin (m+1)=> eventually_all.mpr fun d:Fin (e.val+1)=> h₁ _ _ (Nat.le_of_lt_succ d.isLt)),eventually_all.mpr fun i=> eventually_all.mpr fun d=> eventually_all.mpr fun w=> eventually_all.mpr (he' i d w)] with k hv he h₁ ht
      exact ⟨hv,he,h₁,fun n d v j x hx=> ( (dist_eq_norm ..).symm.trans (dist_comm ..)).trans_le ((ht n d v j x hx).le)⟩
   obtain ⟨i,hi⟩:= (eventually_all.mpr (fun q:Fin (m+1)=>he q)).exists; rw [hX] at hi; exact (hS (v i)).2 ⟨A i, fun j hj=> hi ⟨j,Nat.lt_succ_of_le hj⟩⟩
lemma furnished : ∃ P:ℝ→tower S, ∀ j:ℕ, ∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) j:=by
   let B(x:ℝ)(m:ℕ):= {P:tower S | ∀ j ≤ m,Staff (Y:=Y) h F H x P j}
   let M(x:ℝ):= (Finset.range (glen C.S x+1)).filter (fun m=> (B x m).Nonempty)
   have hz(x:ℝ) {m} (p:m∈M x): (B x m).Nonempty:= (Finset.mem_filter.mp p).2
   obtain ⟨v,x,hx⟩:= (on_crew h F H hZ 0).exists
   let V(x':ℝ):= if h:(M x').Nonempty then (hz x' (Finset.max'_mem (M x') h)).choose else x
   refine ⟨V,fun m=>?_⟩
   filter_upwards [on_crew h F H hZ m,(glen_leads C.S).eventually_ge_atTop m] with i hp hi; have hh : m ∈ M i:= Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi),hp⟩; have he:(M i).Nonempty:=⟨m,hh⟩; unfold V; rw [dif_pos he]; exact (hz i (Finset.max'_mem (M i) he)).choose_spec m (Finset.le_max' _ _ hh)
omit hZ
private lemma angles_staff (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) j)(d:ℕ):∀ᶠ r in trail, obedient F H (P r) d:= (hP d).mono fun _ hi=>hi.spins (Fin.last d)
private lemma fitted_lead (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) j) : Leading F P where
    equivariant d := (angles_staff h F H P hP d).mono fun i hi=>obedient_realH F h H hi
    raised := fun {d e} h=>(hP e).mono fun i hi=> hi.rises (Fin.last e) ⟨d,Nat.lt_succ_of_le h⟩
    unit d := (angles_staff h F H P hP d).mono fun i hi=> hi.unit
    lead n d v j L hl h := by
      refine measured_tensor F (r:=fun r:ℝ=>r) (v:=fun _=>none) (w:=fun _=>v) (l:=trail) self_mem_nhdsWithin d j (fun i=> PoleC C (d i)) hl h ?_ (fun _=>tendsto_const_nhds)
      intro p; rw [Metric.tendstoUniformlyOn_iff]; intro ε he
      obtain ⟨i,hi,ht,h₁,h₂,h₃⟩:= ((eventually_ge_atTop j).and ((eventually_ge_atTop n).and ((eventually_all.mpr (fun i=> eventually_ge_atTop (d i))).and ((size_ascends.eventually (Work.A05.compact_fits hl h)).and (cost_clears.eventually (gt_mem_nhds he)))))).exists
      let n':Fin (i+1):= ⟨n,Nat.lt_succ_of_le ht⟩; let d':Fin n'→ Fin (i+1):= fun x=>⟨d x,Nat.lt_succ_of_le (h₁ x)⟩
      filter_upwards [hP i] with r hp x hx; rw [dist_comm,dist_eq_norm]; exact (hp.checks n' d' p ⟨j,Nat.lt_succ_of_le hi⟩ x (h₂ hx)).trans_lt h₃

lemma leading_chores (P:ℝ→tower S)(hP:Leading F P)(m:ℕ) : ∀ᶠ r in trail, chores r (P r 4) m:=by
   refine eventually_all.mpr fun n=> eventually_all.mpr fun v=> eventually_all.mpr fun j=> ?_
   let d:Caps n:= fun _=>4; let w:MaxwellSlots C d:=fun i=>PoleC C 4 (v i); let V:= Scaling.window (sizeHint m) n
   have hv := hP.lead n d w j V (window_closed ..) (fun x hx=>spaced_conf (cost_pos _) hx.1)
   filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv _ (cost_pos m)] with r hr x hx
   specialize hr x hx; rw [dist_comm,dist_eq_norm] at hr; exact hr.le
include hZ in
/-- Ready to impose a common cap-four X posture. -/
theorem base_stage : ∃ P:ℝ→tower S, PlotX F H Y h (fun r=> P r 4) ∧ (∀ m:ℕ,∀ᶠ r in trail, chores r (P r 4) m) ∧ Leading F P ∧ ∀ d,∀ᶠ r in trail, obedient F H (P r) d := by
   obtain ⟨P,hP⟩:= furnished h F H hZ; have hV := fitted_lead h F H P hP
   exact ⟨P,(hP 4).mono (fun i hi=>hi.angle), leading_chores F P hV,hV,angles_staff h F H P hP⟩
end YM.PhysMS.Frame
