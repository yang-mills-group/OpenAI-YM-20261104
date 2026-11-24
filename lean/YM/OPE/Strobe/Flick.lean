import YM.OPE.Strobe.Flint
/-! # Measure-back independence to all copy origins. Primary tests spatial points enlarged by mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Set
open MergeProof Accent Ribbons ManyCopies Patrol Push Marker Source Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open GridApprox Cells Extra.Multi GridApprox.Nil MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {A:History G}
set_option quotPrecheck false
local notation "K" => Finset
variable {N p i j k : ℕ} {s: i≤N} {F:I→ Config G (A.S.side N p)→ℂ} {Q:Config G (A.S.side i p)→ Poly (Bud I)}
local notation "R" => A.rep N p
local notation "f" => A.S.side N p
local notation "c" => A.S.side i p
local notation "T" => tilesAt A.S p
local notation "β" => A.β N p N
local notation "∆" => (Wilson.partition G f β:ℂ)
-- finite arbitrary frame basis
omit [Fintype I] in -- maybe no omit DecEq
lemma sparrow {o y: Site n}{r:ℕ}: y∈ window o r↔ separation o y ≤ r:= ⟨by rintro ⟨a,h,ha⟩; subst y; exact Work.E08.separation_box_add o h,fun h=>⟨lift (y-o),Work.E08.lift_mem_box h,show wrap n _ + _ = _ from by rw [wrap_lift,sub_add_cancel]⟩⟩
omit [Fintype I] in
lemma island {o: Site n} (r:ℕ) : window o r=(halo r ({o}:Support n):Set _):=by
    ext i; rw [sparrow,Finset.mem_coe,halo_spec]; simp
-- choose whole windows on level k, grows at each finer of same schedule.
def muzzle (Y:Levels G)(i r:ℕ) := r+ 30*(Y.clock.J i+5)
local notation "S" => A.S
variable {o:I→ Site c} {u b:ℕ}
lemma locale (x:Site c) (r:ℕ) {X:Config G c → ℂ}(he: Interior (window x r) X) (ht:i≤ j) : Interior (window (anchor A.S p ht x) (grows A.levels i r ht)) (backTo A N p ht X):=backTo_local A N p (h:=i) le_rfl ht x r (by rw [show anchor A.S p (le_refl i) x = x from (by unfold anchor Ratio.embed Schedule.toDepth; simp only [tsub_self,Schedule.steps]; rw [show ((1:Side).val:ℕ)=1 from rfl,one_smul,wrap_lift])]; exact he)
omit [Fintype I] [DecidableEq I] in
lemma freedom (x y: Site c) (hh:2*muzzle A.levels i u< separation x y) (ht:i≤j) : Disjoint (window (anchor A.S p ht x) (grows A.levels i u ht)) (window (anchor A.S p ht y) (grows A.levels i u ht)):=by
    apply Set.disjoint_left.mpr; intro v hv he; let a:= separation x y; let z:= muzzle A.levels i u; let t:= (S).toDepth ht p; let r:= grows A.levels i u ht; let l:= t.count.val
    have h : l*a ≤ 2*r:= by
       apply le_trans (Corona.below t x y); apply (separation_triangle _ v _).trans; rw [separation_comm v (t.embed y)]; apply (Nat.add_le_add (sparrow.mp hv) (sparrow.mp he)).trans; omega -- termination reducibility
    change 2*z<a at hh; have hz : r ≤ l*z:=by
       apply Nat.cast_le (α:=ℝ) |>.mp
       have he:= scales_budget A.levels i u ht; have hv:= tail_pos A.levels j; have hz : ((z:ℕ):ℝ)= (u:ℝ)+30*((A.levels.clock.J i:ℝ)+5):=by unfold z muzzle; norm_cast
       push_cast; apply le_of_mul_le_mul_left _ ((S).a_pos j); rw [← mul_assoc (S|>.a j),(S).embeds_scale t,hz]; unfold GridApprox.tail at *; unfold r; linarith only [he,hv]
    exact not_le_of_gt ((mul_left_comm 2 l z).trans_lt (Nat.mul_lt_mul_of_pos_left hh t.count.pos) |> lt_of_le_of_lt (Nat.mul_le_mul_left 2 hz)) h
omit [Fintype I] [DecidableEq I] in
lemma patrolling [Fintype I] [DecidableEq I] {t:Side}(X:I→ Config G n→ℂ) {p:I→ Set (Site n)}(hp : ∀ i,Interior (p i) (X i))(hv:∀ i j,i≠j→Disjoint (p i) (p j))(a:Finset I) (W : StepData n t)(w:ℝ)(hw: W.patch.Branches W.kernel G): back W w (fineJob X a)=fineJob (fun i=>back W w (X i)) a:=by
    induction a using Finset.induction_on with
    | empty=>  unfold fineJob; simp_rw [Finset.prod_empty]; exact back_const (W.isKernel hw w) 1
    | @insert x p' h IH=>
       let S':={i|∃ j∈p',i∈p j}; have he:Interior S' (fineJob X p'):=Interior.combines X p' (fun j h=>(hp j).enlarges (fun _ hh=>⟨j,h,hh⟩))
       have hz : Disjoint (p x) S' := by refine Set.disjoint_left.mpr ?_; intro i hx hj; obtain ⟨j,hj,ht⟩:=hj; exact Set.disjoint_left.mp (hv _ _ (ne_of_mem_of_not_mem hj h).symm) hx ht
       have hX (F:I→ Config G n→ℂ) : fineJob F (insert x p') = F x*fineJob F p':=by unfold fineJob; funext i; exact Finset.prod_insert h
       rw [hX,back_factors hw (cylinder_env (hp x)) (cylinder_env he) (hp x).localSites he.localSites hz, IH]; funext i; unfold fineJob; simp [h]
 
section trick
lemma backs_many (H : History G) (ud N pd i l : ℕ) (o : I → Site (H.S.side i pd))
    {X : I → Config G (H.S.side i pd) → ℂ} (a : Finset I)
    (hZ : ∀ r, Cells.Interior (GridApprox.window (o r) ud) (X r))
    (hp : ∀ r j, r ≠ j → 2 * muzzle H.levels i ud < separation (o r) (o j))
    (hh : i ≤ l) : GridApprox.backTo H N pd hh (fineJob X a)=fineJob (fun r => GridApprox.backTo H N pd hh (X r)) a :=by
    induction l,hh using Nat.le_induction with
    | base => simp
    | succ l h IH=> simp_rw [backTo_next H N pd h, IH]; exact patrolling _ (fun j=>locale _ _ (hZ j) h) (fun i j e=>freedom (o i) (o j) (hp i j e) h) a _ _ (H.levels.blocks ..).branches
end trick
omit [Fintype I] [DecidableEq I] in
lemma wind {V:Type} [DecidableEq V] {P:Brigade n V} {o:I→Site n}{X:I→ Config G n→ℂ}(hp:∀ i, Interior (window (o i) u) (X i)) (j:V×I) : Interior (window (P.place o j) u) (P.calls X j):=by
    unfold Brigade.calls Brigade.place; split; exact hp _; next h=>
    let z:=hp j.2; let v:= P.center j.1; let s:= P.spin j.1; have h := (hp j.2).unchanged _ _ (window_affine _ v s.1); unfold stepUp Motion.scalar; split_ifs; exact h.real; exact h
end YM.OPE.Strobe

