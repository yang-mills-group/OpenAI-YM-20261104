import YM.MS.RapidIntegration
import YM.MS.Plane
import YM.MS.CompareSymbol
/-!
# Chart for kernel calculations

Use arbitrary linear routing maps per mode; no preferred constrained last leg
needs to be carried through the estimates. The bounds may depend on the chart.
We'll recover preferred-coordinate Taylor jets where needed. Real external
momenta and their CLMs appear here (dimension continuation uses integer-rank
analogs). Polynomial Ward classification only tests nets on closed bulk lanes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Set Filter Finset Koszul Real
open scoped Topology ContDiff
variable {A ι : Type*} {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Wire (A E P : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] := Legs (Mode A (E →L[ℝ] P))
namespace Wire
def sail (w : Wire A E P) (x:E) : Legs (Mode A P) := w.map fun l=> (l.1,l.2 x)
@[simp] lemma sail_nil (x:E) : sail ([]: Wire A E P) x=[]:=rfl
@[simp] lemma sail_cons (q : Mode A (E →L[ℝ] P)) (w : Wire A E P) x : sail (q::w) x=(q.1,q.2 x)::sail w x := rfl
@[simp] lemma sail_join (q w: Wire A E P) x : sail (q++w) x=sail q x++sail w x:=List.map_append ..
@[simp] lemma sail_net (w : Wire A E P) (x:E) : net (sail w x)=net w x:= by
   induction w with
   | nil => rfl
   | cons a l IH => simp [IH]
@[simp] lemma sail_len (w : Wire A E P) (x:E) : (sail w x).length=w.length:=by simp [sail]
@[simp] lemma sail_base (w : Wire A E P) (x:E) : (sail w x).map Prod.fst=w.map Prod.fst:=by unfold sail; simp only [List.map_map]; rfl
@[simp] lemma sail_degree (p : Sector A) (w : Wire A E P) (x:E) : degree (field p) (sail w x)=degree (field p) w:= by
    induction w with
    | nil => rfl
    | cons i w ih => simp only [sail_cons,degree_cons,ih,field]
lemma sail_scatter (p : Sector A) (w : Wire A E P) (x:E) (K : Shared (Mode A P) ℂ) : scatter (field p) (sail w x) K = scatter (field p) w (fun l r => K (sail l x) (sail r x)) := by
   induction w generalizing K with
   | nil => rfl
   | cons i w ih => rw [sail_cons,scatter_cons, ih,scatter_cons]; simp only [sail_degree,sail_cons,field]

def lift (w : Wire A E P) (L : F →L[ℝ] E) : Wire A F P := w.map fun l=> (l.1,l.2.comp L)
@[simp] lemma lift_sail (w : Wire A E P) (L : F →L[ℝ] E) x : sail (lift w L) x=sail w (L x):=by simp only [sail,lift,List.map_map]; rfl
@[simp] lemma lift_len (w : Wire A E P) (L : F →L[ℝ] E) : (lift w L).length=w.length:= by simp [lift]
@[simp] lemma lift_net (w : Wire A E P) (L : F →L[ℝ] E): net (lift w L)=(net w).comp L:= by
   ext; rw [← sail_net,lift_sail,sail_net,ContinuousLinearMap.comp_apply]
@[simp] lemma lift_base (w : Wire A E P) (L : F →L[ℝ] E): (lift w L).map Prod.fst=w.map Prod.fst:= by simp only [lift,List.map_map]; rfl

def ray (w : Legs (Mode A P)) : Wire A ℝ P := w.map fun l=> (l.1, ContinuousLinearMap.toSpanSingleton ℝ l.2)
@[simp] lemma ray_go (w : Legs (Mode A P)) (x : ℝ) : sail (ray w) x=w.map (fun i=> (i.1,x • i.2)) := by simp only [sail, ray,List.map_map]; rfl
@[simp] lemma ray_sail (w : Legs (Mode A P)) : sail (ray w) 1=w:= by simp
@[simp] lemma ray_net {w : Legs (Mode A P)} : net (ray w)=ContinuousLinearMap.toSpanSingleton ℝ (net w):= by
   apply ContinuousLinearMap.ext; intro x;  rw [← sail_net,ray_go]
   induction w with
   | nil => simp [net]
   | cons a w ih =>
       simp only [List.map_cons, net_cons,ContinuousLinearMap.toSpanSingleton_apply] at *; rw [ih,smul_add]
end Wire

variable {S : Scale ι} {w : Wire A E P} {f g : ι → Row A P ℂ}
open Wire
def Chart (f : ι → Row A P ℂ) (w : Wire A E P) : Kern ι E ℂ:= fun i x=>f i (sail w x)
lemma chart_lift (L : F →L[ℝ] E) (f : ι → Row A P ℂ) (w : Wire A E P) : Chart f (lift w L) = fun i x=> Chart f w i (L x):=by ext; rw [Chart, lift_sail]; rfl
lemma chart_at (f : ι → Row A P ℂ) (i) (x:E) (w : Wire A E P) : Chart f w i x=f i (sail w x):= rfl
lemma agrees_chart (h : ∀ i, Agrees (f i) (g i)) (hw : net w=0) : Chart f w = Chart g w := by funext i x; exact h i _ (by rw [sail_net,hw]; rfl)
lemma equivalent_charts (h : ∀ w : Wire A ℝ P, net w=0 → Chart f w = Chart g w) (i) : Agrees (f i) (g i) := by
    intro w hw; convert congr_fun (congr_fun (h (ray w) (by simp [hw])) i) 1 using 1 <;> rw [Chart, ray_sail]
lemma gather_bound {h : ι →ℝ} {p : Sector A} {f : ι → E → Shared A ℂ} (w : Legs A) (H : ∀ l k, Split l k w → Bound S (fun i x=> f i x l k) h) :
    Bound S (fun i x=> scatter p w (f i x)) h := by
    induction w generalizing f with
    | nil => exact H _ _ .nil
    | cons a w ih=> refine ih (fun l k hs=> (H _ _ hs.left).add ?_); exact Costs.L (ContinuousLinearMap.mul ℝ ℂ (cross (p a) (degree p l))) (H _ _ hs.right)
lemma gather_like {h u : ι →ℝ} {p : Sector A} {f g : ι → E → Shared A ℂ} (w : Legs A) (H : ∀ l k, Split l k w → Like S.full S u (fun i x=> f i x l k) (fun i x=>g i x l k) fun i _=> h i) :
    Like S.full S u (fun i x=> scatter p w (f i x)) (fun i x=> scatter p w (g i x)) fun i _=>h i := by
    induction w generalizing f g with
    | nil => exact H _ _ .nil
    | cons a w ih=> refine ih (fun l k hs=>(H _ _ hs.left).add ?_); exact Like.L (H _ _ hs.right) (ContinuousLinearMap.mul ℝ ℂ (cross (p a) (degree p l)))
end YM.MS.Plane
