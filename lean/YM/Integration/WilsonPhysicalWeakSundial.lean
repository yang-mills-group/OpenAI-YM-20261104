import YM.Integration.WilsonPhysicalWeakRisingStaff
import YM.PhysMS.Frame.Journey

/-! Elect the actual X-calibrated physical frame from the staff that issued the weak Vane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakSundial
open PhysMS PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress Sundial
open MergeProof.East Next.Rank Next.Rank.East Maxwell
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {Y:Ultrafilter (ℕ×ℕ)} (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)
  {Z:Terrace.Arch C} (hZ:Bliss F Y Z H)
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d
open WilsonPhysicalWeakRisingStaff
private lemma axes (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) j)(d:ℕ):∀ᶠ r in trail, obedient F H (P r) d:= (hP d).mono fun _ hi=>hi.spins (Fin.last d)
private lemma leading (P:ℝ→tower S)(hP:∀ j:ℕ,∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) j) : Leading F P where
    equivariant d := (axes h F H P hP d).mono fun i hi=>obedient_realH F h H hi
    raised := fun {d e} h=>(hP e).mono fun i hi=> hi.rises (Fin.last e) ⟨d,Nat.lt_succ_of_le h⟩
    unit d := (axes h F H P hP d).mono fun i hi=> hi.unit
    lead n d v j L hl h := by
      refine measured_tensor F (r:=fun r:ℝ=>r) (v:=fun _=>none) (w:=fun _=>v) (l:=trail) self_mem_nhdsWithin d j (fun i=> PoleC C (d i)) hl h ?_ (fun _=>tendsto_const_nhds)
      intro p; rw [Metric.tendstoUniformlyOn_iff]; intro ε he
      obtain ⟨i,hi,ht,h₁,h₂,h₃⟩:= ((eventually_ge_atTop j).and ((eventually_ge_atTop n).and ((eventually_all.mpr (fun i=> eventually_ge_atTop (d i))).and ((size_ascends.eventually (Work.A05.compact_fits hl h)).and (cost_clears.eventually (gt_mem_nhds he)))))).exists
      let n':Fin (i+1):= ⟨n,Nat.lt_succ_of_le ht⟩; let d':Fin n'→ Fin (i+1):= fun x=>⟨d x,Nat.lt_succ_of_le (h₁ x)⟩
      filter_upwards [hP i] with r hp x hx; rw [dist_comm,dist_eq_norm]; exact (hp.checks n' d' p ⟨j,Nat.lt_succ_of_le hi⟩ x (h₂ hx)).trans_lt h₃

def provisional (day:ℝ→Day C S)(r:ℝ):tower S:=(day r).2.frame

theorem attended (day:ℝ→Day C S)(rises:Tendsto (fun r=>(day r).1) trail atTop)
    (sold:∀ᶠr in trail,Served (Y:=Y) h F H (day r) r):
    ∀m:ℕ,∀ᶠr in trail,Staff (Y:=Y) h F H r (provisional day r) m:=by
  intro m
  filter_upwards [sold,rises.eventually_ge_atTop m] with r booked cap
  exact (booked.2.2 m cap).1

include hZ
private lemma compose_pose (P:ℝ→tower S) (hP:∀ᶠ r in trail, Pilot.AtAngle F h (H:=H) (𝓛:=Y) r (P r 4))
    (hp:Leading F P) (ha:∀ d,∀ᶠ r in trail, obedient F H (P r) d)
    {P':ℝ→change S 4} {φ : E4→ℝ} {x y : ℝ→ℝ}
    (hE: Sundial.Posed H h (fun r=>P r 4) P' x y) (hS:Sundial.ShellNorm P' φ) :
    ∃ Q:ℝ→tower S, (∀ᶠ r in trail, Q r 4=P' r) ∧ localCost trail P Q ∧
      (∀ d,∀ᶠ r in trail,obedient F H (Q r) d) ∧ Leading F Q := by
    let U(r:ℝ):= update (β:=fun d=> change S d) (P r) 4 (P' r)
    have ht:= august F H h hZ hP (leading_chores F P hp) hE hS
    have hC:localCost trail P U:=by
        intro d v; by_cases H:d=4
        · subst H; simp_rw [U,update_self]; exact Dash.arcing ht (tendsto_const_nhds (x:=v))
        unfold U; simp_rw [update_of_ne H,LinearEquiv.symm_apply_apply]; exact tendsto_const_nhds
    have hv(d):∀ᶠ r in trail, obedient F H (U r) d:=by
        by_cases hd:d=4
        · subst d; filter_upwards [(avatar F H h hZ hP (leading_chores F P hp) hS.valid hE hS).spun] with r hR
          unfold obedient U; rw [update_self]; exact hR.align
        unfold obedient U; simp_rw [update_of_ne hd]; exact ha d
    have hx:Adjacent F U trail:= neighboring F (X:=P) (?_) hC
    swap; · intro d v; apply tendsto_const_nhds.congr'; filter_upwards[hp.raised (Nat.le_succ d)] with i hi; rw [← hi,LinearEquiv.symm_apply_apply]
    let Q(r:ℝ):= compatible F (U r); have hQ:localCost trail P Q:= localCost_trans hC (fun d=> fitted_up F hx d)
    have hR:= plan_angle F h H hx hv
    refine ⟨Q,?_,hQ,hR,⟨fun d=> (hR d).mono fun i hi=>obedient_realH F h H hi,fun hc=> accounted F _ _ hc hx,fun d=> (hR d).mono fun i hi=> hi.unit,fun n d v j E hK he=>?_⟩⟩
    · filter_upwards [unchanged4 F h H hx (fun d _=> hv d)] with i hi; unfold Q; rw[hi]; exact update_self ..
    let w(r:ℝ) (i:Fin n):D (d i):= (P r (d i)).symm (Q r (d i) (v i))
    have ht(r:ℝ): measured F none (Q r) v r= measured F none (P r) (d:=d) (w r) r:=funext fun x=> DFunLike.congr_arg _ (funext fun j=> ((P r _).apply_symm_apply _).symm)
    simp_rw [ht]; exact measured_tensor F (r:=id) (v:=fun _=>none) (l:=trail) (w:=w) self_mem_nhdsWithin d j (fun i=>PoleC C (d i)) hK he (fun v=> hp.lead n d _ _ _ hK he) (fun i=> hQ (d i) (v i))


theorem original (day:ℝ→Day C S)(rises:Tendsto (fun r=>(day r).1) trail atTop)
    (sold:∀ᶠr in trail,Served (Y:=Y) h F H (day r) r)
    (reached:∀φ P P',Target.XScheme F h H Y P P' φ → ∃a d e,Target.FieldComparison F H Z P P' a d e):
    Leading F (provisional day) ∧ ∃(J:ℝ→tower S)(P':ℝ→change S 4)(φ:E4→ℝ)(a d e:ℝ→ℝ),
      (∀ᶠr in trail,J r 4=P' r) ∧ Target.XScheme F h H Y (fun r=>provisional day r 4) P' φ ∧
      Target.FieldComparison F H Z (fun r=>provisional day r 4) P' a d e ∧
      localCost trail (provisional day) J ∧ Leading F J ∧ ∀g,∀ᶠr in trail,obedient F H (J r) g:=by
  let P:=provisional day
  have staff:=attended h F H day rises sold
  have lead:=leading h F H P staff
  have obedience:=axes h F H P staff
  have angle:PlotX F H Y h (fun r=>P r 4):=(staff 4).mono fun r s=>s.angle
  obtain ⟨φ,window⟩:=Work.A05.has_window Pith.sail Pith.sail_at
  obtain ⟨P',x,y,pose,norm⟩:=Sundial.spectrum_s F H h hZ angle (leading_chores F P lead) window
  have scheme:Target.XScheme F h H Y (fun r=>P r 4) P' φ:=⟨angle,leading_chores F P lead,⟨x,y,pose⟩,norm⟩
  obtain ⟨a,d,e,comparison⟩:=reached φ _ P' scheme
  obtain ⟨J,same,near,turns,leadingJ⟩:=compose_pose h F H hZ P angle lead obedience pose norm
  exact ⟨lead,J,P',φ,a,d,e,same,scheme,comparison,near,leadingJ,turns⟩

end YM.Integration.WilsonPhysicalWeakSundial
