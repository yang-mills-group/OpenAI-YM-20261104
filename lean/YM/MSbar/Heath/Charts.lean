import YM.MSbar.Heath.Lost
import YM.Work.E02
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U:Config G f}{V:Config G c}{R:Rep G f}{σ C T a y v x δ w:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum
variable (h:Admitted V R S σ C δ T w)
    {κ σ' C' w' T' δ':ℝ}
private lemma ind (A:Set (Config G f))(h:MeasurableSet A) : Envelope (A.indicator (fun _=> (1:ℝ))):= Envelope.piece h (Envelope.const _) (Envelope.const _)
include h
lemma union_bound {A B:Set (Config G f)}(ha: MeasurableSet A)(hb: MeasurableSet B) : chance S R V (A∪B) ≤ chance S R V A+chance S R V B:=by
   apply le_trans ?_ (e_sum V h (ind _ ha) (ind _ hb)).le
   refine nn V h ((ind _ ha).add (ind _ hb)) (ind _ (ha.union hb)) fun i=>?_
   change (A ∪ B).indicator (fun _=>(1:ℝ)) i ≤ A.indicator (fun _=>(1:ℝ)) i + B.indicator (fun _=>(1:ℝ)) i; by_cases ht:i∈A <;> by_cases he:i∈B <;> simp [Set.indicator,ht,he]
lemma complement_zero : chance S R V ∅ = 0:= by unfold chance; rw [Set.indicator_empty]; exact e_const V h 0
lemma join {Z:Type} {P : Z→ Set (Config G f)}(X: Finset Z)(ha:∀ i∈X,MeasurableSet (P i)) : chance S R V (⋃ i∈X,P i) ≤ ∑ i∈X,chance S R V (P i):=by
   induction X using Finset.induction with
   | empty=> simp [complement_zero h]
   | insert i x hx ih=>
     have ht j (he:j∈x): MeasurableSet (P j):=ha _ (mem_insert_of_mem he)
     rw [Finset.set_biUnion_insert,Finset.sum_insert hx]; exact (union_bound h (ha _ (mem_insert_self ..)) (Finset.measurableSet_biUnion _ ht)).trans (add_le_add_right (ih ht) _)
open Tree Bid Pressure Pressure.Stores
variable (F : Forest S.ratio) (e : Edge (Site f))
-- angles unread. Stamp account.
def compass (X:Patch) (K:KernelChoices) (G:Gauge):= (Work.E02.answer G X.L X.J K).choose
def pillar (S:StepData c f) (x : Site c) := (box (macroR S.patch)).image (fun z=>wrap f z+ S.ratio.embed x)
omit h in
lemma weather_pos (G : Gauge) (S:StepData c f) : 0<compass S.patch S.kernel G:= (Work.E02.answer G _ _ _).choose_spec.1
set_option quotPrecheck false
local notation "l₀"=> S.ratio.parent e.1
local notation "W"=> pillar S l₀
-- chart using fixed tree drape
variable {U: Config G f}
def canoe (F : Forest S.ratio)(U : Config G f): Config G f:= Lattice.gauge (F.foldAt U) U
omit h in
lemma canoe_cont : Continuous (canoe F (G:=G)):=by unfold canoe; change Continuous _; apply continuous_pi; intro i; unfold Lattice.gauge; fun_prop
local notation "t₀"=> compass S.patch S.kernel G
local notation "T!"=> R.p.threshold
local notation "c0"=> S.patch.Branches S.kernel G
def breeze (S:StepData c f) : ℝ := (box (macroR S.patch)).card* (Fintype.card PlaqAxes:ℝ)
def brow (S:StepData c f) (G:Gauge) (v t a:ℝ) := v/4 + compass S.patch S.kernel G*(breeze S*t)+ a
def gCost (R:Rep G f)(S:StepData c f) (y w':ℝ) := ((box (macroR S.patch)).card:ℝ)*y*w'
variable {P:Rep G c}
variable (ht : P.Lawful σ' C' T' δ' w')
variable (hw:V∈calm G c v)(hp:v≤P.p.threshold)(hv:0<v)(hb: Decent P.clip P.p) (hk:P.eval=S.push R.beta R.eval)
variable (he:100*macroR S.patch≤ f.val) (hx:1<c.val)(hr:0≤P.beta)(hd : S.patch.Branches S.kernel G)
include h hb he hx hr ht hw hp hv hk hd
open Precision
lemma around (hy:0≤a)(hζ:0≤R.beta) (hh:Psalm S R P.p.threshold y)(hy':0≤y) : chance S R V {U: Config G f |  brow S G v R.p.threshold a < G.chord (canoe (S:=S) F U e)} ≤
    gCost R S y w + Real.exp (ankle P.p P.clip σ' C' δ' T' v w' P.beta) * Real.exp (shellBill G S R.beta - R.beta*S.kernel.penalty*a^2/2) := by
   let d:=brow S G v T! a; let L (U:Config G f):= canoe (S:=S) F U; let H : Set (Config G f):={U |  d < G.chord (L U e)}
   have hz:=hζ; have hm: MeasurableSet H:= (isOpen_lt continuous_const (G.continuous_chord.comp ((continuous_apply e).comp (canoe_cont ..)))).measurableSet
   let Y(i:Site f):Set (Config G f):={U | i ∈ flags T! U}; let A:=⋃ i∈ W, Y i
   have hA(i): MeasurableSet (Y i):= (flags_open ..).measurableSet; have hU : MeasurableSet A := Finset.measurableSet_biUnion _ (fun i _=>hA i)
   have hw' := voids hw hp
   have hJ : chance S R V A ≤ gCost R S y w:=by
       refine (join h W (fun i _=> hA i)).trans ((sum_le_sum (g:=fun _=> y*w) (fun i (_:i∈W)=> probability_flag V h hh hw' hy' i)).trans ?_); have ht : 0≤w:=budget_nonneg ((h.lawful.labels.boundK).choose_spec.2 0)
       rw [sum_const,nsmul_eq_mul]; unfold gCost; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_image_le)) (mul_nonneg hy' ht)
   apply (c_mono V h hm (hU.union (hm.diff hU)) (show H ⊆ A ∪ (H \ A) from (fun i he=> (em (i∈A)).elim (fun h=> Or.inl h) (fun h=> Or.inr ⟨he,h⟩)))).trans -- set proof inspect
   apply (union_bound h hU (hm.diff hU)).trans; apply add_le_add hJ
   let p : Edge (Site c):= (l₀,e.2)
   refine lost S p h ht hw hp hv hb hk (H \ A) (hm.diff hU) hr hd ?_ hy hζ
   intro U hu l hl
   have hα : d < G.chord (L U e):= hu.1
   have hi : Healthy T! W U := Finset.disjoint_left.mpr (fun i hx ht=> hu.2 (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hx,ht⟩⟩))
   have hp': port S l₀ (L U) ≤ breeze S * T!:=by
       refine Work.E01.port_le S (L U) l₀ T! R.p.threshold_pos.le ?_; intro j hj
       rw [show toll (L U) j=_ from SectorMeasure.toll_gauge (F.foldAt U) U j]
       obtain ⟨z,hz⟩:= card_pos.mp hj; obtain ⟨hv,ht,-⟩:= mem_filter.mp hz
       exact le_of_not_gt (fun he=> Finset.disjoint_left.mp hi (mem_image.mpr ⟨z,hv,ht⟩) ((flags_spec ..).mpr ⟨j,List.mem_toFinset.mpr (List.mem_cons_self),he⟩))
   have hZ := SectorMeasure.choice_gauge hd U l (F.foldAt U)
   have hV : SliceSet S F (L U):= fun j hj=> F.compress U j hj
   have hh: S.prediction (L U) l = S.prediction U l:= hZ.2.trans (funext fun i=> by dsimp [Lattice.gauge]; rw [F.fold_root,F.fold_root];simp)
   have hL : S.likelihood (L U) l≠0:=by rwa [show L U=gauge (F.foldAt U) U from rfl,hZ.1]
   have hyq:= (Work.E02.answer G _ _ _).choose_spec.2 _ _ S rfl rfl rfl he hx F (L U) hV V e l (Pressure.wraps S l ((S.likelihood_pos _ _).lt_of_ne hL.symm) l₀)
   let c : ℝ:= t₀; have he : G.chord (Precision.replica S.ratio V e)≤v/4 :=by unfold Precision.replica; split; rw [G.chord_one]; positivity; exact hw _ (Set.mem_univ _)
   have hiV: G.chord (L U e) ≤ G.chord (L U e*(Precision.replica S.ratio V e)⁻¹) + G.chord (Precision.replica S.ratio V e) :=by nth_rw 1 [← inv_mul_cancel_right (L U e) (Precision.replica S.ratio V e)]; exact G.chord_triangle ..
   unfold Cops at hyq; simp only [hh] at hyq; unfold d brow at hα
   split at hyq
   next hC=> exfalso; have hxx:=mul_le_mul_of_nonneg_left hp' (weather_pos G S|>.le); change _ ≤ t₀ * port S l₀ (L U)+0 at hyq; linarith only [hyq,hxx,hiV,he,hα,hy]
   next hC=> have hxx:= mul_le_mul_of_nonneg_left hp' (weather_pos G S|>.le); change G.chord (L U e*(Precision.replica S.ratio V e)⁻¹) ≤ t₀ * port S l₀ (L U) + G.chord (V p*(S.prediction U l p)⁻¹) at hyq; linarith
end YM.MSbar.Heath
