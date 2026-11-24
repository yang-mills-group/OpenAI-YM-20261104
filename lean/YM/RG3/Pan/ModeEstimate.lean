import YM.RG3.Pan.Aria
import YM.RG3.Axial.Stoop
/-! # Actual physical LEFT jets of palette

Bright even for fields *not* satisfying any shell estimates. Basis slots
price is taken only once per differentiated leg, in the physical direction's
true chart. Every path used in palette, including to the common frame, is
included. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan.ModeEstimate
open YM.RG3.Pan Function FreeResolvent Lattice RG Wilson WilsonStartup Next.Rank.Spindle Filter SelectedOrderedKernels WardBin.Lies
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fee covering every finite order of the REAL chart of the ordered-stack
path. Separate horizon jell of moving derivative convention. -/
def harbor (G : Gauge) (k : ℕ) :=
    1+∑ j∈Finset.range (k+1), ∑ i∈Finset.range (k+1), ‖iteratedFDeriv ℝ i (G.mat ∘ chain G j) 0‖
lemma one_le_harbor (G : Gauge) (k : ℕ) : 1 ≤ harbor G k := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _=> Finset.sum_nonneg (fun _ _=> norm_nonneg _)))
lemma harbor_cast (G : Gauge) (k : ℕ) {j:ℕ} (hj : j ≤ k) : Bill k (harbor G k) 1 (G.mat∘chain G j) 0:= by
  constructor
  · exact (chain_smooth G j).contDiffAt.of_le le_top
  intro i hi; rw [one_pow,mul_one]
  apply le_trans _ (le_add_of_nonneg_left zero_le_one (b:=_))
  let C j i:=‖iteratedFDeriv ℝ i (G.mat∘chain G j) 0‖
  exact (Finset.single_le_sum (f:=C j) (fun _ _=> norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans
    (Finset.single_le_sum (f:=fun j=>∑ i∈Finset.range (k+1), C j i) (fun _ _=> Finset.sum_nonneg fun _ _=> norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

lemma orbit_bond (k : ℕ) {j : ℕ} (hj : j ≤ k) (U : Config G n) (v : Slab G n j) (i : Edge (Site n)) (d : ℝ) (hd : 0 ≤ d) (hv : ∀ l, ‖v l i‖ ≤ d):
    GroupHit k (harbor G k) d (fun z=> journey U j v z i) 0:= by
  let L : Panels j→L[ℝ] Panel G j:= ContinuousLinearMap.pi (fun w=> (ContinuousLinearMap.proj w : (Panels j)→L[ℝ] ℝ).smulRight (v w i))
  have hV (w) : ‖L w‖ ≤ d*‖w‖:= by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hd (norm_nonneg _))).mpr; intro b
    change ‖w b • v b i‖ ≤ _; rw [mul_comm d]
    exact (norm_smul_le ..).trans (mul_le_mul (norm_le_pi_norm ..) (hv _) (norm_nonneg _) (norm_nonneg _))
  have h:= Bill.gust L (by rw [map_zero]; exact harbor_cast G k hj) hV zero_le_one hd; rw [one_mul] at h
  let P : G.Mat→L[ℝ] G.Mat:= (ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat (U i))
  have hi:= h.emit P zero_le_one (fun x=> by
    change ‖x*G.mat (U i)‖ ≤ (1:ℝ)*‖x‖; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star ..),one_mul]) hd
  erw [one_mul,show P ∘ (G.mat ∘ chain G j) ∘ L = G.mat ∘ (fun z=> journey U j v z i) from ?_] at hi; swap
  · funext z; change G.mat _ * G.mat _ = G.mat (chug j _ _ i); rw [chug_apply];rfl
  exact hi.cast

lemma increment_bond (k : ℕ) (hk : 1 ≤ k) (U:Config G n) (i : Edge (Site n)):
    GroupHit k (harbor G k) 1 (fun z=>increment U z i) 0 := by
  let L : Directions G n→L[ℝ] Panel G 1 := ContinuousLinearMap.pi (fun _=>ContinuousLinearMap.proj i)
  have h:= Bill.plain L (by rw [map_zero]; exact harbor_cast G k hk) (fun w=>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=> norm_le_pi_norm w i)
  let P : G.Mat→L[ℝ] G.Mat:= (ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat (U i))
  have hi:= h.emit P zero_le_one (fun x=> by
    change ‖x*G.mat (U i)‖ ≤ (1:ℝ)*‖x‖; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star ..),one_mul]) zero_le_one
  erw [one_mul,show P ∘ (G.mat ∘ chain G 1) ∘ L = G.mat ∘ (fun z=>increment U z i) from ?_] at hi; swap
  · funext z; change G.mat ((1*G.lieExp (_)):G.El) * G.mat (U i) = G.mat _; rw [one_mul]; rfl
  exact hi.cast

variable {k b : ℕ} {o : Site n}
def clock (G : Gauge) (k b:ℕ) := 1+2^k*harbor G k*(8*b+4:ℕ)
lemma one_le_clock (G : Gauge) (k b:ℕ) : 1 ≤ clock G k b := le_add_of_nonneg_right (by have:=one_le_harbor G k; positivity)

/-- All routes for palette cost no more than 8*b+4 uses of a physical link,
including retracing inverse links. No hypothesis on the period. -/
def ride {b} (i : Turn b) := paths i.val.1 ++ (square i.val.2.val.1 i.val.2.val.2 ++ Lattice.reverse (paths i.val.1))
lemma rose (U : Config G n) (a : Turn b): registered b U o a = travel (expandAt o U) (0:Cover) (ride a):= by
  unfold registered used central; rw [face_gauge]
  let w:=paths a.val.1; let l := square a.val.2.val.1 a.val.2.val.2; let A:=expandAt o U
  change travel A 0 w * travel A _ l * (travel A 0 w)⁻¹ = travel A 0 (w ++ (l ++ Lattice.reverse w))
  rw [travel_append, stops, travel_append, square_stop, ← stops a.val.1, travel_reverse]
  simp only [w,mul_assoc]
  -- last rw rewrites inside w?
lemma ride_cap (i : Turn b) : (ride i).length ≤ 8*b+4 := by
  unfold ride; have hi:=bounded (faceOrigin i); rw [List.length_append,List.length_append,Lattice.reverse,List.length_map,List.length_reverse, lengths]
  change _ + (4+_) ≤ _; omega

private lemma split_visits {x:Cover}(l l':Walk){y}(hy:y∈visits x (l++l')):
   y∈visits x l ∨ y∈visits (stop x l) l':=by
  induction l generalizing x with
  | nil=> exact Or.inr hy
  | cons a l ih=>
    rcases List.mem_cons.mp hy with h|h
    · exact Or.inl (List.mem_cons.mpr (.inl h))
    exact (ih h).imp_left (fun e=>List.mem_cons.mpr (.inr e))
private lemma reversed_visit (x : Cover) (w : Walk){y}(hy:y∈visits (stop x w) (Lattice.reverse w)): y∈ visits x w:= by
  induction w generalizing x with
  | nil=> exact hy
  | cons a w ih=>
    unfold Lattice.reverse at hy; rw [List.reverse_cons,List.map_append] at hy
    rcases split_visits _ _ hy with h|h
    · exact List.mem_cons.mpr (.inr (ih (x:=x+a.vec) h))
    change y∈ visits (stop (stop (x+a.vec) w) (Lattice.reverse w)) [a.rev] at h
    simp only [reverse_stop,visits,List.mem_cons,List.not_mem_nil,or_false,Step.vec_rev,add_neg_cancel_right] at h
    rcases h with h|h
    · rw [h]; exact List.mem_cons.mpr (.inr (by cases w <;> simp [visits]))
    exact List.mem_cons.mpr (.inl h)
lemma ride_fits (i : Turn b) {y} (hy:y∈visits (0:Cover) (ride i)) : y∈box b:= by
  unfold ride at hy
  rcases split_visits _ _ hy with h|h
  · exact village _ (faceOrigin i) _ h
  rcases split_visits _ _ h with h|h
  · rw [stops] at h; exact face_patch i _ h
  rw [stops, square_stop, show i.val.1=stop (0:Cover) (paths i.val.1) from (stops i.val.1).symm] at h -- rewrites inside w
  exact village _ (faceOrigin i) _ (reversed_visit 0 _ ((show y∈visits _ (Lattice.reverse (paths i.val.1)) from by simpa only [stops] using h)))

def candle (G : Gauge): ℝ:=G.colorScale⁻¹ * ‖(1:G.Mat)‖
lemma candle_pos (G : Gauge):0≤candle G:=by unfold candle; have hg:=G.colorScale_pos; positivity

local notation "hull" => Next.Rank.Spindle.patch
lemma passed (U : E→Config G n) {x : E} {d:ℝ} (hd : 0 ≤ d)
    (hu : ∀ i:Edge (Site n), i∈Room o b → GroupHit k (harbor G k) d (fun z=> U z i) x):
    Bill k (candle G) (clock G k b*d) (fun z=>palette b o (U z)) x:= by
  apply Bill.bundle (candle_pos _) (mul_nonneg (zero_le_one.trans (one_le_clock ..)) hd)
  intro i
  let V(y:E):=expandAt o (U y)
  have hi (j : Edge Cover) (h:j.1∈box b) (h':j.1+step j.2∈box b):
      GroupHit k (harbor G k) d (fun z=>V z j) x:= hu _ (reads (⟨j,h,h'⟩) o).property
  have he:= hymn V 0 (ride i) (zero_le_one.trans (one_le_harbor G k)) hd (box b) (fun _ h=>ride_fits i h) hi
  have hL: 0≤1+2^k*harbor G k*((ride i).length:ℝ):=le_trans zero_le_one (le_add_of_nonneg_right (by have h:=one_le_harbor G k; positivity))
  have hE: (1+2^k*harbor G k*(ride i).length)*d ≤ clock G k b*d:= by apply mul_le_mul_of_nonneg_right _ hd; unfold clock; have:=one_le_harbor G k; gcongr _+?_ * ?_; exact Nat.cast_le.mpr (ride_cap i)
  have hg:=G.colorScale_pos
  have hc := (he.drift (mul_nonneg hL hd) hE (norm_nonneg _)).emit (tint G) (C:=G.colorScale⁻¹) (by positivity) (tint_norm G) (mul_nonneg (zero_le_one.trans (one_le_clock ..)) hd)
  unfold palette; simp only [Function.comp_def] at hc ⊢; simp_rw [rose]; exact hc

lemma stellar (k b : ℕ) (o : Site n) (U : Config G n) : ContDiffAt ℝ (k:ℕ∞ω) (palette b o ∘ increment U) 0:= by
  have hx:= passed (k:=k+1) (b:=b) (o:=o) (increment U) (d:=1) zero_le_one (fun i _=> increment_bond (k+1) (by omega) U i)
  exact hx.smooth.of_le (by exact_mod_cast Nat.le_succ k)

def glitter (p : BudgetPoint)(b:ℕ) := (1+2*(b:ℝ))^p.power
lemma one_le_glitter (p : BudgetPoint)(b:ℕ):1≤glitter p b:=one_le_pow₀ (by simp)
lemma lived (p : BudgetPoint)(o x : Site n) (hx : x∈hull b o) (A:Directions G n) (hA:p.dirBound x A) (i : Edge (Site n)) (h:i∈Room o b):
    ‖A i‖ ≤ glitter p b*p.threshold:= by
  have ht := (doors _).mp (Finset.mem_filter.mp h).2.1; rw [separation_comm] at ht
  have hz := (doors _).mp hx
  have hr : (separation i.1 x:ℝ) ≤ 2*b:= by exact_mod_cast ((separation_triangle i.1 o x).trans ((Nat.add_le_add ht hz).trans_eq (two_mul b).symm))
  rw [mul_comm]; unfold glitter; refine (hA i).trans (mul_le_mul_of_nonneg_left ?_ p.threshold_pos.le)
  gcongr

lemma palette_jets (p : BudgetPoint)(x o:Site n)(U:Config G n)(hx : x∈hull b o){j : ℕ} (A:Slab G n j)(hj:j≤k)(h:∀i,p.dirBound x (A i)):
    Bill k (candle G) ((clock G k b*glitter p b)*p.threshold) (palette b o ∘ journey U j A) 0:= by
  rw [mul_assoc]
  exact passed (journey U j A) (mul_nonneg (zero_le_one.trans (one_le_glitter ..)) p.threshold_pos.le) (fun i hi=>orbit_bond k hj U A i _ (mul_nonneg (zero_le_one.trans (one_le_glitter ..)) p.threshold_pos.le) fun t=>lived p o x hx _ (h t) i hi)

end YM.RG3.Pan.ModeEstimate
