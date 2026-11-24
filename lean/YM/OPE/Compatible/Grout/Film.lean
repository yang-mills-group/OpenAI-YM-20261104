import YM.OPE.Compatible.Yolk.Blot
/-!
 # Reweight an actual sphere by a stencil ledger. Budgets paid once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c₀ f L : Side} {S : StepData c₀ f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X Y Z : Support f} {b:Config G f→ℝ} {c ε:ℝ} -- c shadow remove
lemma Paced.rise (hp:Paced R X S b c) (hy:X⊆Y)(he:c≤ε): Paced R Y S b ε:=⟨inheritance hp.owns hy,hp.meas,hp.pedal,fun i=> (hp.bound i).trans he⟩ -- inheritance namespace uses Config G c allowed
lemma Paced.safe (hp:Paced R X S b c) : 0≤c:=(norm_nonneg _).trans (hp.bound 1)
lemma Paced.product {d:Config G f→ℝ}(hp:Paced R X S b c)(h:Paced R Y S d ε):Paced R (X∪Y) S (b*d) (c*ε):=by
  refine ⟨fun U V H he=>?_,hp.meas.mul h.meas, fun t hh U=> congr_arg₂ (·*·) (hp.pedal t hh U) (h.pedal t hh U),fun i=>?_⟩
  · exact congr_arg₂ (·*·) ((hp.rise subset_union_left le_rfl).owns U V H he) ((h.rise subset_union_right le_rfl).owns U V H he)
  rw [Pi.mul_apply,norm_mul]; exact mul_le_mul (hp.bound _) (h.bound _) (norm_nonneg _) hp.safe

def PaidY (R:Rep G f)(S:StepData c₀ f)(X:Support f)(m:ℕ)(v:Config G f→ℝ)(b:ℝ):Prop:=∃ Y:Support f,X ⊆ Y ∧ Paced R Y S v b ∧ ∀ Z,X⊆Z→coverNumber R.p.B (Z∪Y)≤coverNumber R.p.B Z+m
lemma PaidY.owns (h:PaidY R S X m b ε):Envelope b:=by obtain ⟨x,hJ,h,hx⟩:=h;exact h.env
lemma PaidY.cash (h:PaidY R S X m b ε):∀ U, ‖b U‖≤ε:=by obtain ⟨x,hJ,h,hx⟩:=h;exact h.bound
lemma PaidY.product {q:Config G f→ℝ}{n:ℕ}(h:PaidY R S X m b c)(g:PaidY R S X n q ε):PaidY R S X (m+n) (b*q) (c*ε):=by
    obtain ⟨Y,hY,h,hs⟩:=h; obtain ⟨U,hU,g,hW⟩:=g; refine ⟨Y∪U,hY.trans subset_union_left,h.product g,fun t ht=>?_⟩
    rw [← union_assoc]; exact (hW _ (ht.trans subset_union_left)).trans (((Nat.add_le_add_right (hs _ ht) n)).trans_eq (Nat.add_assoc ..))
lemma prepay (h:Paced R X S b c):PaidY R S X 0 b c:=⟨X,le_rfl,h,fun p hp=>by rw [union_eq_left.mpr hp];rfl⟩
lemma PaidY.smul {A:ℝ}(h:PaidY R S X m b c):PaidY R S X m (A • b) (‖A‖*c):=by
   have hk := (prepay (X:=X) (b:=fun _=>A) (R:=R) (S:=S) (c:=‖A‖) ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _ _=>rfl,fun _=>le_rfl⟩).product h; rw [zero_add] at hk; exact hk
-- let Countable, sum unconstrained
local notation "Atlas_"=> Config G f → ℝ
def Sable (R:Rep G f)(S:StepData c₀ f)(X:Support f)(b:ℝ)(K:Atlas_)(a:ℝ):Prop:=∃ (ι:Type), Countable ι ∧∃ (J:ι→Atlas_)(m:ι→ℕ)(f:ι→ℝ),(∀ i,PaidY R S X (m i) (J i) (f i))∧ SumBudget (fun i=>Real.exp (b*m i)*f i) a∧∀ U, HasSum (fun i=>J i U) (K U)
namespace Sable
lemma fine {ι:Type}{m':ι→ℕ}{J:ι→Atlas_}{v:ι→ℝ} (hp:∀ i:ι, PaidY R S X (m' i) (J i) (v i)) (ht:SumBudget (fun i=>Real.exp (c*m' i)*v i) ε) (hh:0≤c) : SumBudget v ε:=budget_mono ht (fun p=>(norm_nonneg _).trans ((hp p).cash 1)) (fun p=>le_mul_of_one_le_left ((norm_nonneg _).trans ((hp p).cash 1)) (Real.one_le_exp (mul_nonneg hh (by positivity))))
lemma present (h:Sable R S X c b ε)(hh:0≤c): Envelope b ∧ ∀ U,‖b U‖≤ ε:=by
    obtain ⟨ι,hc,J,m,v,h,hp,hB⟩:=h; have ht:=fine h hp hh; have he i:Measurable (J i):=(h i).owns.meas; have hf : Dominated J:=⟨_,ht.2.1,fun p=>(h p).cash⟩
    have hs:= fun i=>(hB i).tsum_eq; have hv U: ‖b U‖≤ε:=by rw [← hs]; exact (norm_tsum_le_tsum_norm (hf.absolute U)).trans (((hf.absolute U).tsum_le_tsum (fun i=>(h i).cash U) ht.2.1).trans ht.2.2)
    exact ⟨⟨(funext hs) ▸ (Measurable.tsum he),_,hv⟩,hv⟩
end Sable
end YM.PhysicalNext.Repeat.Aroma
