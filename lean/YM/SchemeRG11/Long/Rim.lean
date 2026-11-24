import YM.SchemeRG11.Long.Ash
import YM.SchemeRG11.Wilson.Mire
/-! Trimming escort insertion. With arbitrary positive lamp radius R above support.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial
open scoped Classical
variable {G:Gauge} {T:Align.Itinerary} {B:Window}{r R:ℝ}
def gateY(T: Align.Itinerary)(R:ℝ)(i:ℕ):Finset Cover:=(box ⌈R / T.gap i⌉₊).filter (fun x=> Near T R i x)
lemma gate_iff(T:Align.Itinerary)(R:ℝ)(i:ℕ)(x:Cover): x∈gateY T R i ↔ Near T R i x:=by
 rw [gateY,Finset.mem_filter]; refine ⟨And.right,fun h=>⟨?_,h⟩⟩; apply Acorn.wrapcost
 apply (Nat.cast_le (α:=ℝ)).mp; refine le_trans ?_ (Nat.le_ceil _)
 rw [le_div_iff₀ (T.positive _)]; exact le_trans (mul_le_mul_of_nonneg_right (show (diam x:ℝ)≤d x by unfold d; linarith) (T.positive i).le) (by rw [mul_comm]; exact h)
lemma gate_d (T: Align.Itinerary)(R:ℝ):Surround (T:=T) (gateY T R) R:= Eventually.of_forall fun i x hx => (gate_iff T R i x).mp hx
lemma gate_const(T: Align.Itinerary){R:ℝ}(h:R>0)(p:Cover):∀ᶠ i in atTop, p∈gateY T R i:=by
 simp_rw [gate_iff,Near,baseU]; exact (T.cutoff.mul_const _).eventually (ge_mem_nhds (by rw [zero_mul]; exact h))
lemma cord(T:Align.Itinerary)(i:ℕ)(x:Cover): ‖incVec (T.gap i) x‖≤ 2*baseU T i x:=by
 apply le_trans (roof (T.positive i) _); unfold baseU; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_left; · unfold d; linarith
 exact mul_nonneg zero_lt_two.le (T.positive i).le
lemma mantle(x y:Cover):d (x+y)≤d x+d y:=by
 have he:(diam (x+y):ℝ)≤ diam x+(diam y:ℝ):=by exact_mod_cast diam_add x y
 unfold d; linarith
lemma guardian {b r:ℝ}(T:Align.Itinerary)(hb:b<r)(p:Cover):∀ᶠ i in atTop,∀x,Near T b i x→Near T r i (p+x):=by
 filter_upwards [(T.cutoff.mul_const (d p)).eventually (gt_mem_nhds (show 0*d p< r-b by linarith))] with i hi x (hx:baseU T i x ≤_)
 apply le_trans (b:=T.gap i*(d p+d x)); exact mul_le_mul_of_nonneg_left (mantle ..) (T.positive _).le
 rw [mul_add]; unfold baseU at hx; linarith
lemma past (h:B.rOut<R):∀ᶠ i in atTop,∀x, cove T B i x ≠0 → Near T R i x:=by
 filter_upwards [T.cutoff.eventually (gt_mem_nhds (show 0< R-B.rOut by linarith))] with i hi x hp
 refine (allowNear x i).trans ?_; have he:‖incVec (T.gap i) x‖< B.rOut:=by contrapose! hp; apply B.zero_of_le_dist; rw [dist_zero_right]; exact hp
 linarith
lemma escort_cut(h:B.rOut<R) : ∀ᶠ i in atTop, North.covers (cove T B i) (gateY T R i):=by
 obtain ⟨w,hw,Hw⟩:=exists_between h; refine eventually_all_finset (p:=fun (j:Axis) (i:ℕ)=>∀ (x:Cover), x∉gateY T R i → cove T B i x=0 ∧ cove T B i (x-step j)=0) Finset.univ|>.mpr ?_ |>.mono ?_ -- fragile
 swap
 · intro i (hi :∀ j∈ Finset.univ (α:=Axis),∀ x,x∉gateY T R i → cove T B i x=0 ∧ cove T B i (x-step j)=0) x hx
   exact ⟨(hi 0 (Finset.mem_univ _) _ hx).1,fun k=>(hi k (Finset.mem_univ _) x hx).2⟩ -- Lean prop syntax
 intro j _; filter_upwards [past (T:=T) hw,guardian T Hw (step j)] with i hi e x hx
 rw [gate_iff] at hx
 refine ⟨by contrapose! hx; exact le_trans (hi x hx) Hw.le, ?_⟩
 contrapose! hx; specialize e (x-step j) (hi _ hx); rwa [show step j+(x-step j)=x by abel] at e
lemma denseR(h:2*r≤ B.rIn)(j:ℕ)(x:Cover)(hp:Near T r j x): cove T B j x=1:=B.one_of_mem_closedBall (mem_closedBall.mpr (by rw [dist_zero_right]; linarith only [cord T j x,h,show baseU T j x≤ r from hp]))
lemma vacatesR (B:Window)(a:Axis):∃ R>0,∀ᶠ i in atTop,∀ x,Near T R i x→barkS T B a i x=0:=by
 let r:=B.rIn/2; have hr:0<r:= by unfold r; exact half_pos B.rIn_pos
 refine ⟨r/2,half_pos hr,(guardian T (half_lt_self hr) (-(step a))).mono ?_⟩
 intro i hi x hx; unfold barkS; have he:2*r≤ B.rIn:=by unfold r; linarith
 rw [denseR he _ _ (by convert hi x hx using 1; abel),denseR he _ _ (le_trans hx (half_lt_self hr).le),sub_self]
lemma rank_zero {s:Finset (Shaft G)}(h:B.rOut<R):∀ᶠ i in atTop, s ⊆ North.parade (gateY T R i) ∧ ∀ v∈s,cove T B i v.1.1 =1:=by
 have he(v:Shaft G):∀ᶠ i in atTop, v∈ North.parade (gateY T R i) ∧ cove T B i v.1.1=1:=by
   let r:= B.rIn/2; have hr:0<r:= half_pos B.rIn_pos
   filter_upwards [gate_const T hr v.1.1] with i w
   rw [gate_iff] at w; have H: r< R:=(half_lt_self B.rIn_pos).trans (B.rIn_lt_rOut.trans h)
   refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨(gate_iff ..).mpr (le_trans w H.le),Finset.mem_univ _⟩,Finset.mem_univ _⟩, denseR (by unfold r; linarith) _ _ w⟩
 filter_upwards [(eventually_all_finset s).mpr fun i _=> he i] with i hi; exact ⟨fun k hk=>(hi k hk).1,fun k hk=>(hi k hk).2⟩
end YM.SchemeRG11.Long
