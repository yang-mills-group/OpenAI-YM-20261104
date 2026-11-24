import YM.RegulatorIR.Ledger.Pages
import YM.RegulatorIR.Step.Horizontal

/-!
Indexed decks for a possible inversion-quotient family. We pay strict
triangular transitions to a polynomial cap *before* taking any limits here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W Z:Type} {M : W→ℕ} {X Y: Page M→Type}
structure Sky (X Y:Page M→Type) where
 P : W→ℝ
 hp : ∀ w,0<P w
 l : Page M→ℝ
 hl : ∀ w,0<l w
 climb f : l (Flap.prev f) ≤ l f.next
 maps : ∀ i:Page M,Deck (P i.bindW) (X i) (Y i)
 frames : ∀ f:Flap M,GridStep (maps f.prev) (maps f.next)
 sight : ∀ (f:Flap M), Strip (frames f)

namespace Sky
variable (S:Sky X Y)
def census : Post X Y:=⟨fun w=> S.P w.bindW,fun _=> S.hp _,S.l,S.hl,S.maps⟩
def lifts : Batch (fun i:Flap M=> X i.prev) (fun i=>X i.next) (fun i=>Y i.prev) (fun i=> Y i.next):= {period:= fun i=> S.P i.volW,positive:= fun _=>S.hp _,fine:= fun i=>S.maps i.prev,coarse:=fun i=> S.maps i.next,grid:=S.frames}

def ceiling (i:Flap M):= S.l i.next
lemma high (i):0<S.ceiling i:=S.hl i.next

def ceilingRoom := S.lifts.insideRoom S.ceiling S.high
def bar := S.lifts.incoming S.ceiling S.high
def carryUp := S.lifts.incoming (S.l ∘ Flap.prev) (fun _=>S.hl _)

/-- working through interaction order e and moments U -/
structure Primitive (L:Meter W)(e U:ℕ):Prop where
  depth : Poly L fun w=> (M w:ℝ≥0∞)
  -- charges in output length units
  line : Beam (flapL M L) (S.ceilingRoom.cone U) S.lifts.lineL
  add_cost i : i ≤ e → ∀ j, Workday (flapL M L) (S.ceilingRoom.cone U) (fun w=> S.lifts.rails w i j)
  drift : Beam (flapL M L) (S.ceilingRoom.cone U) S.lifts.forecast
  deckLine : ∀ w, Layer.Sym (S.lifts.room w) (S.lifts.room w) (S.lifts.lineL w)
  deckAdd : ∀ w i j,i ≤ e → (S.lifts.room w).Ready (S.lifts.rails w i j)
  deckDrift: ∀ w, Layer.Sym (S.lifts.room w) (S.lifts.room w) (S.lifts.forecast w)
  -- tree/plane replacement geometry
  ground : ∀ w,(S.sight w).Ground
  grade : ∀ w,Vacuum (S.lifts.rails w)
  prices : ∀ b≤U,∀ k ≤ e, SmoothPrice (flapL M L) (fun w=> native _ (S.high w) b) (fun w=> (S.lifts.fine w).pos) (fun w=> (S.lifts.coarse w).pos) (fun w=> (S.sight w).space) k
  charges : ∀ b≤U,∀ k ≤ e, SmoothPrice (flapL M L) (fun w=> onFold _ (S.lifts.positive w) _ (S.high w) b) (fun w=> (S.lifts.fine w).atO) (fun w=> (S.lifts.coarse w).atO) (fun w=> (S.sight w).run) k

/-- *pre*-block small factor; strengthen size selection (where needed) for
building. Weaker powers of L also work for many recurrence lemmas. -/
def Slot (b:ℕ)(c:Flap M→ℝ≥0∞) : Prop:= ∀ w, Layer.row (Function.swap (S.sight w).pole) (S.ceilingRoom.cone b w) id id (c w)
structure Lead (b:ℕ) (c: Flap M→ℝ≥0∞) : Prop where
  down : S.Slot b c
  cap : ∀ w,c w≤1

/-- The two finite conditioned schemes. `cover` generates soft A-coefficients,
`orb` joint conditional coefficients. Evaluation by top Wilson rules still
requires a theorem linking the joint conditional pathway to them. -/
structure Accounts where
  bulk : (w:Page M)→Orders (X w)
  orb : (w:Page M)→Orders (Y w)
  step_v : ∀ w, (S.frames w).pure (bulk w.prev)=bulk w.next
  step_o : ∀ w,(S.frames w).common (orb w.prev)=orb w.next
  top_v : ∀ w, Vacuum (bulk (Page.opening M w))
  top_o : ∀ w, Vacuum (orb (Page.opening M w))

structure Supplies (T:S.Accounts)(L:Meter W)(e U:ℕ): Prop where
  -- cover bounds do not grant comparison estimates
  bulk_price i : i≤ e → ∀ j, Workday (coverL M L) (S.census.cone U) (fun w=> T.bulk w i j)
  bulk_deck : ∀ w i j,i≤ e → (S.maps w).Ready (T.bulk w i j)

namespace Accounts
variable {S:Sky X Y}(T : S.Accounts)
lemma cap_b (h:∀ i, Vacuum (S.lifts.rails i)):∀ w,Vacuum (T.bulk w):= Page.proves T.top_v (fun w hv=> T.step_v w ▸ (GridStep.pure_step _ (GridStep.joint_vac_shape _ hv (h w))))
lemma cap_o (h:∀ i, Vacuum (S.lifts.rails i)):∀ w,Vacuum (T.orb w):= Page.proves T.top_o (fun w hv=> T.step_o w ▸ (GridStep.fold_step _ (GridStep.joint_fold_shape _ hv (h w))))

def change (w:Page M):Orders (Y w):=fun i j=> T.orb w i j-(S.maps w).deckSum (T.bulk w i j)

variable {L: Meter W}{e U : ℕ}
lemma deposit (h:S.Supplies T L e U) (i:ℕ)(he:i≤ e)(j:ℕ): Workday (flapL M L) (S.bar.cone U) fun w=> T.bulk w.prev i j:= by
 have hP : Workday (flapL M L) (S.carryUp.cone U) (fun w=> T.bulk w.prev i j):= (h.bulk_price i he j).us Flap.prev
 exact Post.work_fewer (M:=S.carryUp) (l:=S.ceiling) S.high (fun w=> S.climb w) hP

/-- Mark transmissions. Input here is ONE source object (it may itself be a
product of columns, which is in general necessary, not their independently
transmitted product at every step). -/
structure Report (m:ℕ) where
  main : ∀ w,Orders (X w)
  point : ∀ w,Orders (Y w)
  step_m : ∀ w,(S.frames w).each m (T.bulk w.prev) (main w.prev) = main w.next
  step_p : ∀ w, (S.frames w).island m (T.orb w.prev) (point w.prev) = point w.next
  ceilingM : ∀ w e,Within (e+m) (main (Page.opening M w) e)
  ceilingP : ∀ w e,Within (e+m) (point (Page.opening M w) e)
  same : ∀ w e r, point (Page.opening M w) e r= (S.maps (Page.opening M w)).scroll (main (Page.opening M w) e r)

namespace Report
variable {T}{m:ℕ} (Z:T.Report m)
lemma cap_b (h:∀ i,Vacuum (S.lifts.rails i)) : ∀ w e, Within (e+m) (Z.main w e):=by
 refine Page.proves Z.ceilingM ?_
 intro w hv; rw [← Z.step_m]; exact (S.frames w).each_shape (GridStep.joint_vac_shape _ (T.cap_b h _) (h w)) m hv
lemma cap_o (h:∀ i,Vacuum (S.lifts.rails i)): ∀ w e,Within (e+m) (Z.point w e):=by
 refine Page.proves Z.ceilingP ?_
 intro w hv; rw [← Z.step_p]; exact (S.frames w).island_shape (GridStep.joint_fold_shape _ (T.cap_o h _) (h w)) m hv

def deviation (w:Page M) : Orders (Y w):=fun i j=> Z.point w i j-(S.maps w).scroll (Z.main w i j)
end Report
end Accounts
end Sky
end YM.RegulatorIR.Ledger
