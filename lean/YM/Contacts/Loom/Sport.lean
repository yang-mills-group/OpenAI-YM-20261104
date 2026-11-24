import YM.Contacts.Loom.Ocean
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
open Capture PertExtension.Series Radial Milling
namespace Patch
variable {d a g:ℕ→ℝ}{K:Set ι}
abbrev Trunk (E V : ℕ→Type):Type:= ∀ i,V i→ E i→ℝ
abbrev buoy {F:Type}[Norm F] (x : F) := 1+‖x‖
lemma hovering (x : V i):1≤buoy x:= le_add_of_nonneg_right (norm_nonneg _)
variable (E V)
def stepIn (d ℓ:ℕ→ℝ)(i:ℕ): Type:= ↥(Frame.Bank E d i) × ↥(closedBall (0:V i) (ℓ i))
variable {E V}
abbrev arm (v:stepIn E V d a i) : E i:= v.1.val
abbrev leg (v:stepIn E V d a i) : V i:= v.2.val
lemma belongs (v:stepIn E V d a i) : arm v∈ball (0:E i) (d i) ∧ leg v∈closedBall (0:V i) (a i):=⟨v.1.2,v.2.2⟩
abbrev wish (U:Shelf E V F): Shelf E (stepIn E V d a) F := fun _ j x=> U _ (leg j) x
abbrev Narrow (N:Meter)(k:ℕ)(b:ℝ)(d a:ℕ→ℝ)(U:Shelf E V F):= Budget N (fun _ v=> arm v) k b (wish (d:=d) (a:=a) U)
structure Joint (N:Meter)(k:ℕ)(b:ℝ)(d:ℕ→ℝ)(U:Shelf E V F) :Prop where
   globally: ∃ S:ℕ,N.Funds (fun i p=> ∀ z:V i,∀ x∈Frame.Bank E d i, Brush k (p*(buoy z)^S) 1 (U i z) x) b
variable {U u v:Shelf E V F} {w:Shelf E V (fun _=>ℝ)}
namespace Joint
lemma ascend (h:Joint N k p d u)(he:p≤q)(hj:j≤k)(hm:∀ᶠ i in atTop, v i=u i): Joint N j q d v:= by
   obtain ⟨s,h⟩:= h.globally; refine ⟨s,h.lift he (hm.mono fun i hi _ _ h j x e=>?_ )⟩; rw [hi]; exact (h j x e).smaller hj
lemma sum (h:Joint N k p d u)(he: Joint N k p d v): Joint N k p d (u+v):= by
   obtain ⟨s,h⟩:= h.globally; obtain ⟨t,ht⟩:= he.globally; refine ⟨s+t,h.fold ht (Eventually.of_forall fun i _ _ hp hQ h he z x e=>?_ )⟩; rw [add_mul]; apply ((h z x e).gathering (he z x e)).climb; swap; exact le_rfl
   gcongr <;> first | exact hovering _ | omega
lemma opp (h:Joint N k p d u): Joint N k p d (-u):= by obtain ⟨s,h⟩:=h.globally; exact ⟨s,h.lift le_rfl (Eventually.of_forall fun i _ _ h z x e=> (h z x e).opposite)⟩
lemma zero : Joint (V:=V) (E:=E) (F:=F) N k p d 0:= by
   refine ⟨0, 0, Meter.Rush.zero, Eventually.of_forall fun i=> ⟨le_rfl, fun z x _=>?_⟩⟩; rw [Pi.zero_apply,zero_mul]; exact Brush.offer.mpr ⟨contDiffAt_const,fun j _=> by change normJ j (fun _:E i=> (0:F i)) x≤_; rcases j with _|j <;> unfold Blaze.normJ <;> simp⟩
lemma tally {ι:Type}(s:Finset ι)(A:ι→Shelf E V F)(h:∀ i∈s,Joint N k p d (A i)): Joint N k p d (∑ i∈s,A i):= by induction s using Finset.induction with|empty=>simpa using zero (V:=V) (F:=F) (N:=N) (E:=E) (k:=k) (p:=p) (d:=d)|insert v w hw ih=> rw [sum_insert hw]; exact sum (h v (mem_insert_self ..)) (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma constant {F : ∀ i,V i → Y i} (hq: N.Funds (fun i p=> ∀ j:V i, ‖F i j‖ ≤ p*(buoy j)^l) r): Joint (E:=E) N k r d (fun i v _=>F i v):= ⟨l,hq.lift le_rfl (Eventually.of_forall fun _ _ _ h j x e=> (Brush.certified zero_le_one (F _ j)).climb (h _) le_rfl)⟩
lemma weighted (h:Joint N k p d u)(ht:N.Rush q f)(he:p+q=r): Joint N k r d (fun i x=> f i • u i x):= by
   obtain ⟨s,h⟩:= h.globally; refine ⟨s,h.loft (f:=fun i=> ‖f i‖) (Meter.absolute ht) (Eventually.of_forall ?_) (Eventually.of_forall fun _=> norm_nonneg _) he⟩; intro i _ hx h z x e; rw [mul_assoc]; exact (h z x e).smul (f i)
lemma scale (h:Joint N k p d u)(r:ℝ):Joint N k p d (r • u):= h.weighted (Rush.settle _) (add_zero _)
lemma walk (f:ℕ→ℝ)(h:N.Rush p f): Joint (E:=E) (V:=V) N k p d (fun i _ _=>f i) := by
   refine ⟨0, (fun i=>‖f i‖),Meter.absolute h,Eventually.of_forall fun i=>⟨norm_nonneg _,fun y x e=>?_⟩⟩; rw [pow_zero,mul_one]; exact Brush.certified zero_le_one _
lemma linear (A:∀ i,F i→L[ℝ] Y i) (hA:N.Rush q (fun i=>‖A i‖))(h:Joint N k p d u)(hp:p+q=r): Joint N k r d (fun i j=> A i∘ u i j):= by
   obtain ⟨s,h⟩:=h.globally; refine ⟨s,h.loft hA (Eventually.of_forall fun i a ht h x j e=> by rw [mul_assoc]; exact (h x j e).report _ (le_refl _)) (Eventually.of_forall fun _=> norm_nonneg _) hp⟩
lemma multiply {U U':Trunk E V} (h:Joint N k p d U)(he:Joint N k q d U')(hr:p+q=r): Joint N k r d (U*U'):= by
    obtain ⟨s,f,hf,H⟩:=h.globally; obtain ⟨t,g,hg,G⟩:= he.globally; refine ⟨s+t, _, (hf.times hg hr).bind ((3:ℝ)^k),?_⟩;
    filter_upwards [H,G] with i hi ht; refine ⟨by have hp:=hi.1; have hh:=ht.1; exact mul_nonneg (mul_nonneg hp hh) (by positivity), fun v x e=>?_⟩; refine ((hi.2 v x e).paints (ht.2 v x e) |>.trim).climb ?_ le_rfl; exact (le_of_eq (by norm_num; rw [pow_add]; ring))
lemma sheet {P: Lamp F}(h : Joint N k p d u)(he : N.Rush r (fun i=> normJ j (P i) 0)): Joint N k (r+p*j) d (fun i y x=> jet (P i) j (u i y x)):= by
    let S (i:ℕ): Tensor.T (F i) ℝ j:=iteratedFDeriv ℝ j (P i) 0; let V':= fun i (y:V i) (x:E i)=> Tensor.diagonal (S i) (u i y x); have hv:Joint N k (r+p*j) d V':= by
        obtain ⟨w,f,hf,H⟩:=h.globally; refine ⟨w*j,_,he.times (((hf.bind ((3:ℝ)^k)).powers j)) rfl,?_ ⟩; filter_upwards [H] with i hi; let t(v:V i):=(buoy v)^w; refine ⟨mul_nonneg (norm_nonneg _) (by have hh:=hi.1; positivity), fun y x e=>?_⟩; apply (Budget.shine (Ω:=fun _=> S i) (hi.2 y x e) (Brush.certified zero_le_one _)).climb _ le_rfl; rw [pow_mul]; exact (le_of_eq (by rw [mul_right_comm _ (buoy y^w),mul_pow,mul_assoc]))
    exact Joint.scale hv _
variable {U:ℕ→ Trunk E V}
lemma stepJ (h:∀ i≤j,Joint N k p d (U i))(hp:0≤p) (v k':ℕ)(ht:k'≤j): Joint N k (p*v) d (stair U v k'):= by
   induction v generalizing k' with
   | zero=> simp only [Nat.cast_zero,mul_zero,stair]; split; exact walk (fun _=>1) (Rush.settle _); exact zero
   | succ v ih=>
     unfold stair branch; refine Joint.tally _ _ (fun i hi=> ?_); have he:= HasAntidiagonal.mem_antidiagonal.mp hi; exact Joint.multiply (ih _ (by omega)) (h i.2 (by omega)) (by push_cast; ring)
lemma rollerJob (h:∀ i≤j,Joint N k p d (U i))(hp:0≤p) (v k':ℕ)(ht:k'≤j): Joint N k (p*v) d ((rol U v) k'):= by
   unfold rol; rw [Finset.sum_apply]; apply Joint.tally; intro i hi; have ht':(i:ℝ)≤ v:= Nat.cast_le.mpr (by have he:=mem_range.mp hi; omega); exact ((stepJ h hp _ k' ht).scale (i.factorial:ℝ)⁻¹).ascend (mul_le_mul_of_nonneg_left ht' hp) le_rfl (Eventually.of_forall fun _=>rfl)
end Joint
end Patch
end
end YM.Contacts.Loom
