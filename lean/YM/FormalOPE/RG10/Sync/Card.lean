import YM.FormalOPE.RG10.Sync.Kernels
/-!
 # Paying ranks simultaneously in Material and open field ledger
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp
open MvPolynomial (totalDegree)
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {I B:Type}[Fintype I] [Fintype B]
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable (L:Layout I E)(Q: Layout B F)

lemma linear_one (f:Module.Dual ℝ E): totalDegree (stroke L f)≤1:= by
 unfold stroke; apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le (fun i _=>?_)); exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X])
omit [Fintype I] in
lemma spur_rank (d:F→ₗ[ℝ] E)(i:I)(r:ℕ): Guard (spurs L Q d i) r 1:= by
 intro j _; unfold spurs; rw [coeff_C]; split; exact (linear_one _ _).trans (Nat.le_add_right ..); simp -- note split no pattern
-- layout independent rank
 def stock (d:ℕ)(T:Ticket E): Prop:= ∀ (I:Type)[Fintype I](L: Layout I E)(r:ℕ),Guard (digital L T) r d -- binder Inst avoid
namespace stock
lemma inside (d:ℕ)(T:Ticket E)(h:stock d T)(r:ℕ): Guard (digital L T) r d:= h _ _ _
lemma change_era (L:Layout I E)(Q:Layout B F)(u:F→ₗ[ℝ] E){v:Ticket E}{r d:ℕ}(h:Guard (digital L v) r d): Guard (digital Q (boost u v)) r d := (reassess L Q u v) ▸ Guard.prep h (spurs L Q u) (fun i=> spur_rank L Q u i r)
lemma announce (L:Layout I E){T:Ticket E}{d:ℕ}(h:∀ r,Guard (digital L T) r d) : stock d T:= by
 intro J inst Q r; simpa (config:={unfoldPartialApp:=false}) only [show boost (LinearMap.id : E→ₗ[ℝ] E) T=T from by apply Stack.into; intro x; rw [caught]; rfl] using change_era L Q LinearMap.id (v:=T) (h r)
lemma mul {u v:Ticket E}{i j:ℕ}(h:stock i u)(g:stock j v) : stock (i+j) (u*v):= by intro J H Q r; rw [_root_.map_mul]; exact (h J Q r).mul (g J Q r)
lemma zero : stock 0 (0:Ticket E):= fun I H L r=> by rw [map_zero]; exact Guard.zero
lemma add {u v: Ticket E}{d:ℕ}(h:stock d u)(g:stock d v): stock d (u+v):= by intro J H Q r; rw [_root_.map_add]; exact (h J Q r).add (g J Q r)
lemma sub {u v: Ticket E}{d:ℕ}(h:stock d u)(g:stock d v): stock d (u-v):= by intro J H Q r; rw [map_sub]; exact (h J Q r).sub (g J Q r)
lemma exponential {u:Ticket E}(h:stock 0 u): stock 0 (Stack.exponential u):= by intro J H Q r; rw [authority]; exact Guard.ignited _ (h J Q r)
variable [FiniteDimensional ℝ E]
 def ordinary : Layout (Space E) E:= (Module.finBasis ℝ E).equivFun
lemma bought (d:F→ₗ[ℝ] E){v:Ticket E}{n:ℕ}(h:stock n v): stock n (boost d v):= fun _ _ Q r=> change_era ordinary Q d (h _ ordinary r)
omit [FiniteDimensional ℝ E]
lemma only (u: Ticket E)(i:ℕ): coeff i (digital L u)= ink L (coeff i u):= coeff_map ..
lemma clipped {u: Ticket E}(h: stock 0 u)(n:ℕ): stock 0 (plate n (coeff (n+1) u)):= by
 intro J H Q r i _; rw [only,plate,coeff_monomial]; split
 · rename_i e; subst i; rw [← only]; exact h _ Q (n+1) _ le_rfl
 simp
lemma cycle_h {u: Ticket E}(h:stock 0 u)(n:ℕ): stock 0 (cycle u n):= by induction n with
                                                                         | zero => exact zero
                                                                         | succ i ih=> exact ih.add (clipped (h.sub ih.exponential) i)
lemma canteen {u:Ticket E}(h:stock 0 u): stock 0 (decant u):= by
 intro J H Q r i he; rw [only,receded u i i le_rfl,← only]; exact cycle_h h i _ Q r i he
end stock
end YM.FormalOPE.RG10.Sync
