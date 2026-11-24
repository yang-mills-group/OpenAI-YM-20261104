import YM.Contacts.Loom.Sport
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Patch
open Capture
open scoped ENNReal
variable {d D g:ℕ→ℝ} {n:ℕ} [∀ i,FiniteDimensional ℝ (E i)] [∀ i,MeasurableSpace (V i)][∀ i,BorelSpace (V i)]
abbrev pole {s:E i} : E i:= s
variable {U W:Trunk E V}{μ: ∀ i,Measure (V i)} [∀ i,IsProbabilityMeasure (μ i)]
structure Shell (N:Meter)(μ:∀ i,Measure (V i))(D:ℕ→ℝ) : Prop where
   full (k:ℕ) : ∀ᶠ i in atTop, Integrable (fun x: V i=> (buoy x)^k) (μ i)
   powers (k:ℕ)(p:ℝ): N.Rush p fun i=> ∫ x: V i in (closedBall (0:V i) (D i))ᶜ, (buoy x)^k ∂μ i

abbrev coast (D:ℕ→ℝ) (V:ℕ→Type)[∀ i,NormedAddCommGroup (V i)](i:ℕ) := closedBall (0:V i) (D i)
-- f body weight analytic at all uses measurability.
def Board (D:ℕ→ℝ)(U:Trunk E V): Prop:= ∀ᶠ i in atTop,∀ y∈ Frame.Bank E D i, Measurable (fun x=> U i x y)
def stay (μ:∀ i,Measure (V i))(D:ℕ→ℝ)(U: Trunk E V): Lamp E:= fun i y=>∫ x in coast D V i, U i x y ∂μ i
def gone (μ:∀ i,Measure (V i))(D:ℕ→ℝ)(U: Trunk E V): Lamp E:= fun i y=>∫ x in (coast D V i)ᶜ,U i x y ∂μ i
def weight (μ:∀ i,Measure (V i))(U: Trunk E V): Lamp E:= fun i y=>∫ x,U i x y ∂μ i
def leaf (f: ∀ i,E i→F i): Shelf E (fun i=> ↥(Frame.Bank E d i)) F := fun i _=> f i
abbrev Direct (N:Meter) (k:ℕ)(p:ℝ)(d:ℕ→ℝ) (f:∀ i,E i→F i):= Budget N (Frame.Port E d) k p (leaf f)
namespace Board
lemma sum (h:Board d U)(he:Board d W): Board d (U+W):=(h.and he).mono fun i hi z hz=> (hi.1 z hz).add (hi.2 z hz)
lemma opp (h: Board d U) : Board d (-U):= h.mono fun i hi z hz=> (hi z hz).neg
lemma sub (h:Board d U)(he:Board d W): Board d (U-W):=(h.and he).mono fun i hi z hz=> (hi.1 z hz).sub (hi.2 z hz)
lemma fin (s: Finset ι)(v:ι→Trunk E V)(h:∀ i∈s, Board d (v i)): Board d (∑ i∈s,v i) := by induction s using Finset.induction with| empty => simp; exact Eventually.of_forall fun i _ _=> measurable_const|insert v s hv ih=> rw [sum_insert hv]; exact Board.sum (h v (mem_insert_self ..)) (ih (fun _ hi=>h _ (mem_insert_of_mem hi)))
end Board
section eigen
variable (h: Shell N μ D)(hs: Board d U)(hp:Narrow N k p d D U)
omit h
include hs hp
abbrev Fits (μ:∀ i,Measure (V i))(d:ℕ→ℝ)(U: Trunk E V)(s:∀ i,Set (V i)):= ∀ᶠ i in atTop,∀ x∈ Frame.Bank E d i,IntegrableOn (fun y=> U i y x) (s i) (μ i)
lemma warmer : Direct N k p d (stay μ D U) ∧ Fits μ d U (coast D V) := by -- need instance
   obtain ⟨f,hf,H⟩:= hp.cap; let s:=coast D V; let F i (x:E i):= (s i).indicator (fun y:V i=> U i y x)
   have hh : ∀ᶠ i in atTop, 0≤ f i ∧ ∀ x∈Frame.Bank E d i, IntegrableOn (fun y:V i=> U i y x) (s i) (μ i) ∧ Brush k (f i) 1 (stay μ D U i) x := by
      filter_upwards [H,hs] with i hi hx; refine ⟨hi.1,fun x hy=>?_⟩; let e:=ball (0:E i) (d i); have hq y (hy:y∈ e): Measurable (F i y):= (hx y hy).indicator measurableSet_closedBall
      have hk := (isOpen_ball.mem_nhds (show x∈e from hy)); have hb x (hx:x∈ e) (y:V i): Brush k (f i) 1 (fun x => F i x y) x := by
         unfold F; by_cases hm:y∈s i; · simp_rw [indicator_of_mem hm]; exact hi.2 (⟨x,hx⟩,⟨_,hm⟩)
         simp_rw [indicator_of_notMem hm]; exact (Brush.certified zero_le_one (0:ℝ)).climb ((by simp : ‖(0:ℝ)‖=0).trans_le hi.1) le_rfl
      let g:=fun _: V i=> f i; obtain ⟨hβ,hγ⟩ := Meristem.points (F i) (μ i) (j:=k) ⟨g,integrable_const _,by filter_upwards [hk] with x hx using hb x hx⟩ (by filter_upwards [hk] with x hx using hq x hx)
      have ht: (fun z=> ∫ y,F i z y ∂μ i) = stay μ D U i := funext fun _=> integral_indicator measurableSet_closedBall
      exact ⟨(integrable_indicator_iff measurableSet_closedBall).1 hγ.self_of_nhds, ht ▸ (hβ.buds g (integrable_const _) zero_le_one (by simp [g]) (Eventually.of_forall (hb x hy)))⟩
   exact ⟨⟨_, hf,hh.mono fun i hi=> ⟨hi.1,fun x=> (hi.2 _ x.2).2⟩⟩, hh.mono fun i hi z hz=> (hi.2 z hz).1⟩
omit hp
variable (hr:Joint N k p d U)
include h hr
lemma cool (v:ℝ): Direct N k v d (gone μ D U) ∧ Fits μ d U (fun i=> (coast D V i)ᶜ):= by
   obtain ⟨s,f,hf,H⟩:=hr.globally; let X i:= (coast D V i)ᶜ; let V₀ i x:E i→ℝ:= U i x; let W (i:ℕ):= (μ i).restrict (X i); let u i (v:V i):= buoy v ^s; let Φ i:= ∫ y,u i y ∂W i; have hh:= hf.times (h.powers s (v-p)) (show p+(v-p)=v by ring)
   have h:∀ᶠ i in atTop,0≤f i* Φ i ∧ ∀ x∈Frame.Bank E d i, Integrable (fun v=> U i v x) (W i) ∧ Brush k (f i*Φ i) 1 (gone μ D U i) x:= by
      filter_upwards [h.full s,hs,H] with i hp hx hb; have hu x:0 ≤ u i x:= pow_nonneg (zero_le_one.trans (hovering x)) _ ; let g x:= f i*u i x; refine ⟨mul_nonneg hb.1 (integral_nonneg hu),fun x ht=>?_ ⟩; have he:=isOpen_ball.mem_nhds (show x∈ball (0:E i) (d i) from ht); have hI : Integrable g (W i):= Integrable.integrableOn (hp.const_mul _); obtain ⟨h,h'⟩:= Meristem.points (swap (U i)) (W i) (j:=k) ⟨g,hI,by filter_upwards [he] with t ht y using (hb.2 y t ht)⟩ (by filter_upwards [he] with t ht using (hx _ ht)); exact ⟨h'.self_of_nhds,h.buds g hI zero_le_one (integral_const_mul ..|>.le) (Eventually.of_forall fun t=>hb.2 _ _ ht)⟩
   exact ⟨⟨_,hh,h.mono fun i hi=> ⟨hi.1,fun v=>(hi.2 _ v.2).2⟩⟩,h.mono fun i hi x hx=> (hi.2 _ hx).1⟩
end eigen
end Patch
end
end YM.Contacts.Loom
