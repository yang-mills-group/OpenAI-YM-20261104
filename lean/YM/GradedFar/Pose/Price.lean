import YM.GradedFar.Pose.Debrief

/-!
# Prices of C5 on just the requested stock: keep the compacta and labels
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff

-- general uniform O(.)
section budgets
variable {I E U J W : Type} [NormedAddCommGroup E] {L : Filter I} {g v : I → ℝ} {m k : ℕ} {x y : I → U → E}

/-- uniform on `U`, any clocks. -/
def Terms (L : Filter I) (g : I → ℝ) (x : I → U → E) := (Function.uncurry x)=O[comap Prod.fst L] (fun z : I × U=> g z.1)
lemma Terms.of_be (h : ∃ C : ℝ, ∀ᶠ i in L,∀ u:U, ‖x i u‖ ≤ C*‖g i‖) : Terms L g x := by
  obtain ⟨C,h⟩:= h; exact IsBigO.of_bound C ((tendsto_comap.eventually h).mono (fun u hu=>hu u.2))
lemma Terms.price (h : Terms L g x) : ∃ C : ℝ,0<C ∧ ∀ᶠ i in L,∀ u:U, ‖x i u‖ ≤ C*‖g i‖ := by
  obtain ⟨C,hC,h⟩:= IsBigO.exists_pos h
  exact ⟨C,hC,(eventually_comap.mp h.bound).mono fun i h u=> h (i,u) rfl⟩
lemma Terms.of_bound (D : ℝ) (h : ∀ᶠ i in L, ∀ u : U, ‖x i u‖ ≤ D * g i) (hp : ∀ᶠ i in L, 0 ≤ g i) : Terms L g x :=
  of_be ⟨D, (hp.and h).mono fun i ⟨h,H⟩ u=> by rw [Real.norm_of_nonneg h]; exact H u⟩
lemma Terms.mono (h : Terms L g x) (hy : g=O[L] v) : Terms L v x := IsBigO.trans h (hy.comp_tendsto tendsto_comap)
lemma Terms.tee (h : Terms L g x) (he : ∀ᶠ i in L,∀ u:U, x i u=y i u) : Terms L g y :=
  IsBigO.congr' h ((tendsto_comap.eventually he).mono fun z he=> he z.2) (EventuallyEq.refl ..)
lemma Terms.eq (h : Terms L g x) (he : ∀ i u, x i u=y i u) : Terms L g y := h.tee (Eventually.of_forall he)
lemma Terms.add (a : Terms L g x) (b : Terms L g y) : Terms L g (fun i u=> x i u+y i u) := IsBigO.add a b
lemma Terms.sub (a : Terms L g x) (b : Terms L g y) : Terms L g (fun i u=> x i u-y i u) := IsBigO.sub a b
lemma Terms.blind {x:I→E}(h : x=O[L] g) : Terms L g (fun i (_:U)=> x i) := h.comp_tendsto tendsto_comap
lemma Terms.sum {x : J → I → U → E} (s : Finset J) (h : ∀ j∈s, Terms L g (x j)) : Terms L g (fun i u=>∑ j∈s,x j i u) := IsBigO.sum h
abbrev Proper (L : Filter I) (x : I→U→E) := Terms L (fun _=>1) x
lemma Proper.bounded (B : ℝ) (h : ∀ᶠ i in L,∀ u:U,‖x i u‖≤B) : Proper L x :=
  Terms.of_bound B (h.mono fun i h u=>by rw [mul_one]; exact h u) (Eventually.of_forall fun _=> zero_le_one)
lemma Proper.fixed (x : E) : Proper L (fun (_:I) (_:U)=>x) := Proper.bounded _ (Eventually.of_forall (fun _ _=> le_refl ‖x‖))
section
variable {x y : I→U→ℂ}
lemma Terms.mul (h : Terms L g x) (q : Terms L v y) : Terms L (fun i=> g i*v i) (fun i u => x i u*y i u) := IsBigO.mul h q
lemma Terms.left (h : Terms L g x) (q : Proper L y) : Terms L g (fun i u=> x i u*y i u) := by simpa only [mul_one] using Terms.mul h q
lemma Terms.right (q : Proper L y) (h : Terms L g x) : Terms L g (fun i u=> y i u*x i u) := (h.left q).eq (fun i u => mul_comm (x i u) (y i u))
end
open Filter
lemma Terms.jet {x : I→W→E}{s : U → W} (h : Terms L g x) : Terms L g (fun i u=> x i (s u)) := by obtain ⟨C,hC,h⟩:= h.price; exact Terms.of_be ⟨C,h.mono fun i h u=> h _⟩
end budgets

variable {G : Gauge} {n m d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
variable {F : Plans G d}
include d
/-- C5 using MLM `F` with W fields. We need only individual field requests (no
norms on the entire infinite book). Reminder this is BEFORE homogeneous adjustment.
t here is the projection `t'_ℓ`, not already our measured theta. -/
abbrev Confirmed (F : Plans G d) (q k : ℕ) (t : ℝ → ℝ) (u : ℝ → Normalize.Change G d)
    (K : Set (Points n)) (v : Tags G d n) : Prop := Terms τ (fun r=> g r^k)
      (fun r (x:↥K) => F r n x.val v - crop q (t r) (line N x.val (stand (u r) ∘ v)))

variable (Y : ℝ → Prediction G d) (u : ℝ → Normalize.Change G d) (t : ℝ → ℝ)
variable (compP : ∀ n x, ∀ᶠ r in τ, ContinuousOn (fun p=> F r n p x) (conf n))
  (full : ∀ n (x:Tags G d n) (y:Test n), ∀ᶠ r in τ, Y r n y x=y.applyTo (fun p=> F r n p x))
  (fixed : ∀ᶠ r in τ,(N.store.measure d).D (Y r)=(N.store.measure d).D (reference G d))
  (D : Fray (N.store.measure d))
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H compP full
lemma precise (v : Normalize.Window G d) (q k : ℕ)
    (asks : Confirmed N F q k t u (tsupport v.t) v.p) :
    (fun r=>watch v (Y r)-watch v (recruit (stand (u r)) (foresee N M d q (t r))))=O[τ] (fun r=>g r^k) := by
  obtain ⟨B,hB,h⟩:= asks.price
  apply IsBigO.of_bound (Read.Value v.t*B)
  filter_upwards [h,full v.n v.p v.t,compP v.n v.p] with r hr he hf
  let x : Points v.n → _ := fun x=>F r v.n x v.p
  let y : Points v.n → _ := fun x=> crop q (t r) (line N x (stand (u r) ∘ v.p))
  have ht : ContinuousOn y (tsupport v.t) := by
    unfold y line; simp only [crop_eq]; simp_rw [coeff_mk]
    exact continuousOn_finsetSum _ (fun i _=> ((birth N M H d).light _ _ _).const_mul _ |>.mono v.t.tsupport_subset)
  change ‖Y r v.n v.t v.p-(foresee N M d q (t r)) v.n v.t _‖ ≤ _
  rw [he, weighted N M H]
  change ‖v.t.applyTo x-v.t.applyTo y‖ ≤ _
  rw [← Read.smear_sub _ (hf.mono v.t.tsupport_subset) ht, mul_assoc]
  exact Read.value_le _ ((hf.mono v.t.tsupport_subset).sub ht) (fun x hx=> hr ⟨x,hx⟩)

variable (ht : Tendsto t τ (𝓝 0)) (hc : Tendsto (fun i=> guide G d (u i)) τ (𝓝 0))
include fixed hc ht
lemma landed (q k : ℕ) (asks : ∀ i:Fin D.n, Confirmed N F q k t u (tsupport (D.scope i).t) (D.scope i).p) :
    (fun i=>guide G d (u i))=O[τ] (fun r=>g r^k) := by
  let R r:= recruit (stand (u r)) (foresee N M d q (t r))
  let s r i:= watch (D.scope i) (Y r) - watch (D.scope i) (R r)
  have paid (i:Fin D.n): (fun r=> s r i)=O[τ] (fun r=>g r^k) := precise N M Y u t compP full H (D.scope i) q k (asks i)
  have paid := isBigO_pi.mpr paid
  obtain ⟨B,hB,h⟩:= paid.exists_pos
  apply IsBigO.of_bound (2*(‖D.stamps‖*B))
  filter_upwards [h.bound,fixed,itinerary_fare N M H D q ht u hc] with r hr cost bound
  -- above p:= binder
  have he : D.stamps (s r)=guide G d ((N.store.measure d).D (reference G d) - (N.store.measure d).D (R r)) := by
    rw [← cost]; change guide G d (D.tally _) = _
    rw [show s r=(fun i=>watch (D.scope i) (Y r-R r)) from funext fun i=> (map_sub ..).symm]
    rw [D.equal, map_sub]
  have hw := le_trans (ContinuousLinearMap.le_opNorm D.stamps (s r)) (mul_le_mul_of_nonneg_left hr (norm_nonneg D.stamps))
  rw [he, map_sub,norm_sub_rev] at hw
  rw [map_sub] at bound
  calc
   _ ≤ _ := bound
   _ ≤ 2*(‖D.stamps‖*(B*‖g r^k‖)) := mul_le_mul_of_nonneg_left hw (by norm_num)
   _ = _ := by ring
end
end YM.FVA2.GradedFar.Pose
