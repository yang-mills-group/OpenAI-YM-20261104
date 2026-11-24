import YM.PhysMS.Frame.Stage
import YM.TraceExtension.Endpoint

/-! # Meter at UV lengths with X calibration *on this very meter*. Both
    X pillars P and P' can be lifted along the filtration, but choose P
    already by *all-horizon* considerations before making the calibration
    pose. `P'` differs from that by a finite scheme change which we are free
    to and do extend through all columns, including eventual rising. Because
    it's near identity -- for these leading (not subleading) checks -- we can
    propagate the accuracy into its higher frame extension at all lengths.
    Future matching arguments can turn the calibration into a transport and
    do a different exact scheme; must then retain accuracy at the specified
    coupling-power, which isn't implied by proximity lemma here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress Sundial
open MergeProof.East Next.Rank Next.Rank.East Maxwell
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {Y:Ultrafilter (ℕ×ℕ)} (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)
  {Z:Terrace.Arch C} (hZ:Bliss F Y Z H)
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d
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

/-- On anyone for whom the `stress` specification can be produced we can
    fix the frame and coupling coherently. No new β postulate at our continuous lengths. -/
lemma coupled (hV : ∀ χ P P', Target.XScheme F h H Y P P' χ → ∃ κ d e, Target.FieldComparison F H Z P P' κ d e) :
    ∃ P' : ℝ → change S 4, ∃ (P Q : ℝ → tower S) (φ : E4→ℝ) (a d e : ℝ→ℝ),
      (∀ᶠ r in trail, Q r 4=P' r) ∧ Target.XScheme F h H Y (fun r=>P r 4) P' φ ∧
      Target.FieldComparison F H Z (fun r=>P r 4) P' a d e ∧ localCost trail P Q ∧
      Leading F P ∧ (∀ d,∀ᶠ r in trail, obedient F H (P r) d) ∧ Leading F Q ∧
      ∀ d,∀ᶠ r in trail, obedient F H (Q r) d := by
    obtain ⟨P,hP,hM,hp,hB⟩:= base_stage h F H hZ
    obtain ⟨φ,hφ⟩:= Work.A05.has_window Pith.sail Pith.sail_at
    obtain ⟨P',x,y,hx,hs⟩:= Sundial.spectrum_s F H h hZ hP hM hφ
    have ht : Target.XScheme F h H Y (fun r=>P r 4) P' φ :=⟨hP,hM,⟨x,y,hx⟩,hs⟩
    obtain ⟨κ,d,e,he⟩:= hV φ (fun r=>P r 4) P' ht
    obtain ⟨Q,hq,hE,hF,hQ⟩:= compose_pose h F H hZ P hP hp hB hx hs
    exact ⟨P',P,Q,φ,κ,d,e,hq,ht,he,hE,hp,hB,hQ,hF⟩

universe u
omit hZ H in
lemma meter_found (hX : Target.Result.{u} F h) : ∃ (H : (Bel C.book).Hierarchy) (Z : Terrace.Arch C) (l : Ultrafilter (ℕ × ℕ)),
    Bliss F l Z H ∧ ∃ (P P' : ℝ → change S 4) (Q : ℝ → tower S) (φ : E4→ℝ) (a d e : ℝ→ℝ),
      (∀ᶠ r in trail, Q r 4=P' r) ∧ Target.XScheme F h H l P P' φ ∧
      Target.FieldComparison F H Z P P' a d e ∧ Leading F Q ∧
      ∀ d,∀ᶠ r in trail, obedient F H (Q r) d := by
    obtain ⟨H,Z,l,hl,-,hr⟩:= hX.stress
    obtain ⟨P',P,Q,φ,a,d,e,hp,hP,hF,-,-,-,hQ,hE⟩:= coupled h F H hl hr
    exact ⟨H,Z,l,hl,_,P',Q,φ,a,d,e,hp,hP,hF,hQ,hE⟩
end YM.PhysMS.Frame
