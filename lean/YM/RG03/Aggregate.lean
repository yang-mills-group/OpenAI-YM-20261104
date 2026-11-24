import YM.RG03.BoardCost
/-! Bundle helpers with the ACTUAL output common domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Cost
open RG Wilson Lattice Work.G07 Boards Tight PathWords
open scoped BigOperators Matrix.Norms.Frobenius ContDiff Classical Topology
variable {G:Gauge} {n:Side} {P:BudgetPoint} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {o:Site n} {X:Support n}{ι:Type*}

lemma render_local (T:Token G E ι)(r:List (Board ι))(o:Site n){l:ℕ}(hr:∀ i∈r,radius i l) : LocalOn (cage l o) (render T r o) := by
  induction r with
  | nil => intro U V _; rfl
  | cons a r ih =>
    intro U V e; simp only [render_cons]; rw [price_local T (hr _ List.mem_cons_self) o U V e,ih (fun i hi=>hr _ (List.mem_cons_of_mem a hi)) U V e]
lemma render_invariant (T:Token G E ι)(r:List (Board ι))(o:Site n)(ht:Tight.Together T) : GaugeInvariant (render T r o) := by
  induction r with
  | nil => intro u U; rfl
  | cons a r ih => intro u U; simp only [render_cons]; rw [(price_invariant ht a o) u U, ih u U]
variable [Fintype ι]
lemma render_continuous (T:Token G E ι)(r:List (Board ι))(o:Site n):Continuous (render T r o) := by
  induction r with
  | nil => exact continuous_const
  | cons a r ih => exact (price_continuous T a o).add ih
lemma render_vanish (T:Token G E ι)(r:List (Board ι))(o:Site n){s:ℕ}(hr:∀ i∈r,s ≤ grade i) : Vanishes s (render T r o) := by
  induction r with
  | nil => exact ⟨contDiff_const,fun j _=>by rw [show incident _ = (0:Directions G n→E) from rfl,iteratedFDeriv_zero]; rfl⟩
  | cons a r ih => exact ((price_vanish T a o).shorten (hr _ List.mem_cons_self)).add (ih (fun j hj=>hr _ (List.mem_cons_of_mem a hj)))

lemma render_pays (T:Token G E ι)(o:Site n)(P:BudgetPoint)(r:List (Board ι)){K l m Z:ℕ}
    (hl: r.length ≤ Z) (hr:∀i∈r,m ≤ grade i ∧ grade i ≤ K ∧ radius i l) :
    Pays P o (cage l o) (render T r o) (Z * bill P T l K m) := by
  have he : Pays P o (cage l o) (render T r o) (r.length*bill P T l K m) := by
    clear hl; induction r with
    | nil => simpa using! (LeftBound.const (r:=(1:ℝ)) (k:=P.order) (D:=P.dirBound o) (Z:=Healthy P.threshold (cage l o)) zero_le_one (0:E))
    | cons a r ih =>
      rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]
      exact (priced_tail T a P o (hr a List.mem_cons_self).2 (hr a List.mem_cons_self).1).add (ih (fun i hi=>hr i (List.mem_cons_of_mem a hi)))
  exact he.more (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hl) (bill_nonneg P T l K m))

lemma external_quote (T:Token G E ι) (o:Site n)(P:BudgetPoint)(r:List (Board ι)){K l m Z:ℕ} {X:Support n}
    (hX:cage l o ⊆ X)(hl:r.length ≤ Z)(hr:∀i∈r,m≤grade i ∧ grade i ≤K ∧ radius i l) :
    P.supBounds o X (render T r o) (Z*bill P T l K m) := by
   have h := render_pays T o P r hl hr |>.budget
   exact ⟨h.1,fun U hU j hj he=>h.2 U (hU.mono_left hX) j hj he⟩

lemma render_regular (T:Token G E ι)[MeasurableSpace E][BorelSpace E](r:List (Board ι))(o:Site n)(P:BudgetPoint){l K:ℕ}
    (hr:∀ i∈r, bounded l K i)(ht:Tight.Together T){X:Support n}(hX:cage l o⊆X) : P.Regular X (render T r o) := by
  have h:=render_pays T o P r (Nat.le_refl _) (fun i hi=>⟨Nat.zero_le _,hr i hi⟩) |>.smooth
  refine ⟨(fun U V e=>render_local T r o (fun i hi=>(hr i hi).2) U V (agrees_mono e hX)), (render_continuous ..).measurable,
    render_invariant T r o ht,fun U hU =>(h [] (Nat.zero_le _) U).contDiffAt.of_le (by exact_mod_cast le_top (a:=(P.order:ℕ∞))),fun U hU a t hl => h.has hl.le U a⟩
end YM.RG03.Cost
