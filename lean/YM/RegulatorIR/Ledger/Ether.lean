import YM.RegulatorIR.Ledger.Source

/-! Finiteness for derivations of cover norms along the walk. Distinct from
polynomial uniform bounds. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {r e p u b m:ℕ}{c t : Flap M→ℝ≥0∞}{x:W→Room}{s:W→ℝ≥0∞}{L:Meter W}

def note {X:Type}(T:Packet X 0):ℝ := T Fin.elim0
lemma quotaNote {X:Type}(T:Packet X 0){A:Tariff X}(B:Premium A): markQ B T = ‖note T‖ₑ:= by unfold markQ quota; rw [tsum_eq_single Fin.elim0]; simp [Premium.width,Tariff.diameter,note]; exact fun b hb=> (hb (Subsingleton.elim ..)).elim

lemma unit_car (c : ℝ≥0∞)(h:c≠⊤)(L:Meter Unit): Carry L 1 (fun _=>c):= Carry.regular (Poly.standard _ h)
lemma census_cover {Z:Page M→Type} {e r:ℕ} {T:(w:Page M)→Orders (Z w)}{A:(w:Page M)→ Tariff (Z w)} {B:∀ w,Premium (A w)} (w)(h:markQ (B w) (T w e r)≠⊤) (L:Meter Unit): Claim L (fun _:Unit=>B w) 1 (fun _=>T w e r):=unit_car _ h L

def reportOut (R:(w:Page M)→Orders (X w))(m:ℕ) w:= (S.frames w).each m (T.bulk w.prev) (R w.prev)
lemma lines_tag (h:S.Primitive L p b) (hy:u≤b): Beam (flapL M L) ((S.lifts.insideRoom S.ridge S.ridge_pos).cone u) S.lifts.lineL:= beam_fewer (M:=S.ceilingRoom) (l:=S.ridge) S.ridge_pos S.ridge_more (S.ceilingRoom.descent h.line hy)
lemma bound_cost (w:Flap M)(R:Orders (X w.prev))(G:S.Primitive L p b)(B:S.Supplies T L p b)
   (h:∀ i ≤ p, ∀ j,0<j→markQ (S.yard x u w) (R i j)≠⊤) (hy:u≤b)(m:ℕ):∀ i≤p,∀ r,
     markQ (S.coverQ x u w.next) ((S.frames w).each m (T.bulk w.prev) R i r)≠⊤:=by
 intro i he r
 let l:= S.ridge w; let p':= fun _:Unit=> l
 let k := fun _:Unit=> w
 let A : Batch (fun _:Unit=>X w.prev) (fun _:Unit=>X w.next) (fun _:Unit=>Y w.prev) (fun _:Unit=>Y w.next):= {period:= fun _=> S.P w.volW,positive:= fun _=> S.hp _,fine:=fun _=> S.maps w.prev,coarse:= fun _=>S.maps w.next,grid:= fun _=> S.frames w}
 let D:= (flapL M L).us k
 let C:= A.insideRoom p' (fun _=>S.ridge_pos w)
 have hz: Beam D (C.cone u) A.lineL:= Beam.us (S.lines_tag G hy) k
 have hh : Beam D (C.cone u) A.forecast:= Beam.us (S.get_drift G hy) k
 have hc (e) (hx:e≤p) j :markQ (S.yard x u w) (R e j)≠⊤:=by cases j with
  | zero=> rw [quotaNote]; finiteness
  | succ j=> exact h e hx _ (by omega)
 let Z:= A.incoming p' (fun _=> S.ridge_pos w)
 let z:= fun _:Unit=>x w.volW
 let P:= A.outgoing p' (fun _=> S.ridge_pos w)
 have ht e (hx:e≤p) j: Claim D (Z.rooted z u) 1 (fun _=>R e j):= unit_car _ (hc e hx j) D
 have he' : Claim D (P.rooted z u) 1 fun _=> (S.frames w).each m (T.bulk w.prev) R i r-(S.frames w).pullI (offer (firstChannel (S.maps w.prev) (S.maps w.next)).native (R i r)):=by
   apply Batch.beam_mark A (fun _=> T.bulk w.prev) (fun _=> R) (fun _=> GridStep.joint_vac_shape _ (T.cap_b G.grade _) (G.grade w)) ?_ hz hh (fun e j he _=> ht e (by unfold Earlier at he;omega) j) (fun _=>ENNReal.one_ne_top) (fun _=>hc i he r)
   intro i' hi j
   have hD := S.lifts.fine_work (T.deposit B i' (hi.trans he) j) (G.add_cost i' (hi.trans he) j)
   exact Workday.us (Post.work_fewer (M:=S.ceilingRoom) S.ridge_pos (l:=S.ridge) S.ridge_more (S.ceilingRoom.writes hD hy)) k
 have hβ : Claim D (P.rooted z u) 1 fun _=> (S.frames w).pullI (offer (firstChannel (S.maps w.prev) (S.maps w.next)).native (R i r)):= A.out_post ((A.onto_bill (ht i he r)).draft_budget hh)
 have ht' := he'.add hβ
 simp_rw [sub_add_cancel] at ht'
 exact Claim.cost ht' () ENNReal.one_ne_top
lemma preserves (R:(w:Page M)→Orders (X w))(G:S.Primitive L p b)(B:S.Supplies T L p b)
   (H:∀ w i,i≤p →∀ r,0<r→markQ (S.coverQ x u (Page.opening M w)) (R (Page.opening M w) i r)≠⊤) (hy:u≤b)(m:ℕ)
   (hc:∀ w i,i ≤ p →∀ r,0<r → markQ (S.coverQ x u (Flap.next w)) (R w.next i r- S.reportOut T R m w i r)≠⊤): ∀ w i,i ≤ p → ∀ r, markQ (S.coverQ x u w) (R w i r)≠⊤:=by
 refine Page.proves ?_ ?_
 · intro w i hi r; cases r with
   | zero=> rw [quotaNote]; finiteness
   | succ j=> exact H w i hi _ (by omega)
 intro w hv i he r
 cases r with
 | zero=> rw [quotaNote]; finiteness
 | succ r=>
    let Z:= S.reportOut T R m w i (r+1)
    have hz: markQ (S.coverQ x u w.next) Z ≠ ⊤:= S.bound_cost T w (R w.prev) G B (fun e he j _=> ne_top_of_le_ne_top (hv e he j) (Post.on_fewer (M:=S.camp) S.ridge_pos (fun w=> S.radius_climb w) (x:=step_center M x) w _)) hy _ _ he _
    apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hc w i he (r+1) (by omega),hz⟩)
    exact (show markQ _ (R w.next i (r+1)- Z+Z) ≤ markQ (S.coverQ x u w.next) (R w.next i (r+1)-Z)+markQ _ Z from quota_add ..) |> fun h=> by simpa only [sub_add_cancel] using h
end YM.RegulatorIR.Ledger.Sky
