import YM.Comparison.Density.Mirrors.Interior
/-!
# Real prices of the mirror move

Inactive mask payments bound WITHOUT differentiating into a failed
configuration. `transport_mirror` exposes all hypotheses. Flags have the
`UsesFinal` support; the `inspected` enlargement is compulsory on actual
link reads (encoded by that predicate). This move finishes the regular
norm clause on short symmetric translation packets. Canonical affine read
and exponential marker/flag partner re-expression are still separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors
open Function Lattice RG Wilson Filter WardBin.Lies AnalyticBridge.SectorAffine.Offset
open PhysicalNext.Repeat Transport MeasureTheory AnalyticBridge.CouplingShape
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n b : Side} (B : BudgetPoint) (L : LinkTube G) (f : Links ℤ G.El→ℝ)

private lemma exchange (U : Config G b) (x : Site b) (r : Side) (hp : 2*(r.val+3) < n.val)
    (hu : flags B.threshold U=∅) (o : Site n) : ∃ V : Config G n,
    Healthy B.threshold (neighborhood r.val o) V ∧
      Agrees (Lattice.box r.val) (expandAt o V) (expandAt x U) := by
  let V (e : Edge (Site n)):= expandAt x U (lift (e.1-o),e.2)
  let z : Side := ⟨r.val+3,by omega⟩
  have ht (e : Edge Cover) (he : e.1∈Lattice.box z.val) : expandAt o V e= expandAt x U e := by
    obtain ⟨c,i⟩:=e; change expandAt x U (lift (wrap n c+o-o),i)=_
    rw [add_sub_cancel_right,lifts c he hp]
  have hy : Lattice.box r.val ⊆ Lattice.box z.val:= by
    intro i hi; obtain ⟨ha,hb⟩:= Lattice.box_test.mp hi; have hv:r.val ≤ z.val:= by change _ ≤ r.val+3; omega
    exact Lattice.box_test.mpr ⟨fun j=> by have h:=ha j; omega,fun j=> by have h:= hb j; omega⟩
  refine ⟨V,?_ ,fun e h₁ _=>ht e (hy (show e.1∈Lattice.box _ from h₁))⟩
  apply Finset.disjoint_left.mpr; intro i hi hh
  rw [neighborhood_iff] at hi; obtain ⟨⟨y,p⟩,hp',he⟩:= (flags_spec ..).1 hh
  have hP : separation o y≤ r.val+1:= by
    have hb : i∈ neighborhood 1 y := local_square (y,p) hp'
    rw [neighborhood_iff,separation_comm y] at hb
    exact (separation_triangle o i y).trans (Nat.add_le_add hi hb)
  let a:= lift (y-o)
  have heA : a∈Lattice.box (r.val+1):=Work.E08.lift_mem_box hP
  let W:= square p.val.1 p.val.2
  have hE (v) (hv : v∈visits a W): v∈Lattice.box z.val:= by
    have hit : ∀ j : Cover, ∀ l : ℕ,j∈Lattice.box l → ∀ i : Axis,j+step i∈Lattice.box (l+1):= by
      intro j l h i; obtain ⟨h,h'⟩:= Lattice.box_test.mp h
      apply Lattice.box_test.mpr; constructor <;> intro k <;> have hk:=h k <;> have hl:= h' k <;> simp only [Pi.add_apply,Nat.cast_add,Nat.cast_one,Lattice.step_apply] <;> split <;> omega
    have mono {l : ℕ} (hl:l≤z.val) : Lattice.box l ⊆ Lattice.box z.val:= by
      intro i hi; obtain ⟨ha,hb⟩:= Lattice.box_test.mp hi
      exact Lattice.box_test.mpr ⟨fun j=> by have h:=ha j; omega,fun j=> by have h:= hb j; omega⟩
    simp only [W, square_corners,List.mem_cons,List.not_mem_nil,or_false] at hv
    have hz : z.val=r.val+3:= rfl
    rcases hv with h|h|h|h|h <;> subst v
    · exact mono (by omega) heA
    · exact mono (by show r.val+1+1≤_; omega) (hit _ _ heA _)
    · exact hit _ _ (hit _ _ heA _) _
    · exact mono (by show r.val+1+1≤_; omega) (hit _ _ heA _)
    exact mono (by omega) heA
  have h : travel (expandAt o V) a W = travel (expandAt x U) a W :=
      travel_local _ _ _ _ fun e h _=> ht e (hE _ h)
  rw [travel_at, show wrap n a+o=y from by unfold a; simp,travel_at] at h
  change B.threshold < G.chord (travel V y W) at he
  rw [h] at he
  exact lt_irrefl _ (lt_of_lt_of_le he (local_chord (G:=G) (X:=Finset.univ) (by
    change Disjoint _ (flags _ U); rw [hu]; simp) (wrap b a+x,p) (Finset.mem_univ _)))

def issue (k : Side) (a : ℝ) := a+∑ j : Fin 5, |multiplier j| * ((Fintype.card (Site (quad (advance k j))):ℝ)*a)

lemma flag_sup (r k : Side) (hn : 2*(r.val+3)<n.val) (d : ℕ) (hk : k.val+4≤d) (a : ℝ) (ha : 0≤a)
    (hf : LocalOn (Lattice.box r.val) f)
    (he : ∀ (o : Site n) U, ‖maskCost B f r.val o U‖ ≤ a) (o : Site n) (U : Config G n) :
    ‖flagLog B f r.val k d o U‖≤ issue k a := by
  have hz (j : Fin 5) (x : Site (quad (advance k j))) (s : Site n) :
      ‖masked B.threshold (neighborhood d s) (test f (advance k j) s x) U‖≤ a := by
    let K:=advance k j
    by_cases hu:Healthy B.threshold (neighborhood d s) U
    · rw [masked_eq _ _ _ _ hu]
      have hi:K.val≤d:= by change k.val+j.val≤_; have hp:=j.isLt; omega
      have hK:= tiled_healthy B K s U (Finset.disjoint_of_subset_left (neighborhood_mono hi) hu)
      obtain ⟨V,hV,H⟩:= exchange B _ x r hn hK o
      change ‖f _‖≤ _; rw [← hf _ _ H]
      simpa only [maskCost,masked_eq B.threshold _ _ _ hV,comp_apply] using he o V
    rw [masked_ne _ _ _ _ hu,norm_zero]; exact ha
  unfold flagLog; simp only [Pi.sub_apply]; apply (norm_sub_le ..).trans
  apply add_le_add (he o U); unfold joint; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=>?_
  dsimp only []; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum fun j _=> hz i j _).trans_eq ?_)
  simp

def packetBudget (k : Side) (s : ℕ) (w d e : ℝ) := ∑ j : Fin 5, |multiplier j| * tileBudget B L (advance k j) s w d e

theorem transport_mirror (r k : Side) (o : Site n) (D : ℕ) {w d e : ℝ} {m s : ℕ} (hR : Room B n L D w)
    (hB : k.val+4<D) (hm : B.order ≤ m) (hs : s ≤ m) (hk : r.val<k.val)
    (hN : 4*r.val < n.val) (hd : 0≤d) (he : 0≤e) (hM : Measurable f) (hL : LocalOn (Lattice.box r.val) f)
    (hg : GaugeInvariant f) (h : Ordinary f n s e) (hf : ∀ y : Arms r G, ‖y‖ ≤ w → Through m (Transport.chart r f) y d) :
    B.Regular (neighborhood D o) (restored f k o) ∧
      B.supBounds o (neighborhood D o) (restored f k o) (packetBudget B L k s w d e) := by
  have hp i : (advance k i).val<D:= by change k.val+i.val<D; have hp:=i.isLt; omega
  have hr i : r.val< (advance k i).val:= by change r.val<k.val+i.val; omega
  let F (j:Fin 5):= multiplier j • weightAt f (advance k j) o
  have hv i : B.Regular (neighborhood D o) (F i):=
    AnalyticBridge.CouplingShape.reg_scale _ (weight_regular B L f r _ _ _ hR (hp i) hm hM hL hg hf)
  constructor
  · exact PhysicalNext.Repeat.Meadow.regularA _ fun i _ => hv i
  exact Trio.sup_S (B:=B) F _ Finset.univ _ _ (fun i _=>hv i) (fun i _=>
    AnalyticBridge.CouplingShape.sup_scale _ (weight_sup B L f r _ o _ hR (hp i) hm hs (hr i) hN hd he hL hg h hf))

end YM.Comparison.Density.Mirrors
