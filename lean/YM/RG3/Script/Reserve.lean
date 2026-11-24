import YM.RG3.Script.Lending

/-! # Keep another support exponent through the actual Test merger.

Use the SAME credit poly and stamp as Test. Thus personal coupons on
reclosed drawers don't need to be inflated with extra transports; actually
retain both their strongly priced per-site and per-root sums. The precondition
is on the actual dictionary in the Test and the actual Books at their
positions before merger. Can't use unless there are stronger purchases
(at least a+1 here). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Reserve
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition Push.Local Source Estate Picnic
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
 open Extra.Trajectories
variable {n : Side}{V ι : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge} {w:V→ℝ}
  {P : Rep G n}{p : BudgetPoint}

lemma hit_down {Z:ι→Support n}{a b c : ℝ}{N:ℕ}{f:ι→ℝ}(h : Hit Z N f b c)(hf:∀ i,0≤f i)(ha:a≤b):Hit Z N f a c:= by
  intro x; refine budget_mono (h x) (fun i=>?_ ) (fun i=>?_ )
  · split; exact mul_nonneg (hf _) (Real.exp_pos _).le; rfl
  split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by gcongr)) (hf _); rfl

variable [Countable ι] [Nonempty V](D : Article ι p G R ζ)(a : Bands R P)
  (slot : ι→ℕ)
variable (H:D.Hosting P slot)(hd:D.Sound)(hw:∀ i,0 < w i) {y:ι→Poly R} (he:∀ i U,Width.Covered (D.flow i U) (y i)) {b c : ℝ} (hB : p.supportExponent ≤ b)
  (h:Hit D.span p.B (fun i=> Poly.price w (y i)) b c)
include H hd hw he h hB

lemma supplier :
    let t:=Article.voucher slot ζ D.span y
    let T:=D.impression a slot
    let Z(k:ℕ×ℕ):=(P.activities.forced k.1).support
    let r(k:ℕ×ℕ):=T.marks k.1 k.2
    (∀ i j,0≤t (i,j) ∧ ∀ U,‖T.entries i j U‖ ≤ t (i,j) ∧
      (t (i,j)>0 → ∀ v∈(r (i,j)).val,ζ v∈Z (i,j))) ∧
    Hit Z p.B (fun i=> Poly.toll w (r i)*t i) b c ∧
    ∀ v, SumBudget (per p.B b w r Z t v) c:= by
  intro t T Z r
  have hx:= (D.chosen_profile a slot H hd hw he (hit_down h (fun i=> Poly.nonnegative hw _) hB)).1
  let e:=Article.imprint (R:=R) slot
  let u:=Article.usury ζ D.span y
  have hi:Injective e := fun x y h=> pin_injective (congrArg Prod.snd h)
  have he s:t (e s)=u s:= hi.extend_apply ..
  have hneg i (ha:i∉Set.range e):t i=0:=Function.extend_apply' _ _ i ha
  have hl : ∀ i j,0≤t (i,j) ∧ ∀ U,‖T.entries i j U‖ ≤ t (i,j) ∧ (0<t (i,j) →∀ v∈(r (i,j)).val,ζ v∈Z (i,j)):= by
    refine fun i j=> ⟨(hx i j).1,fun U=>⟨(hx i j).2 _,?_⟩⟩; intro hz
    by_cases h:(i,j)∈Set.range e; swap; exact (by rw [hneg _ h] at hz; exact (lt_irrefl _ hz).elim) -- equality not_gt?
    obtain ⟨s,hs⟩:=h; rw [← hs,he s] at hz; unfold u Article.usury at hz; split at hz
    next h => rw [← hs]; change ∀ v∈ ((D.impression a slot).marks (slot s.1) (pin s)).val,ζ v∈(P.activities.forced (slot s.1)).support; rw [D.marked_pin a slot _ s, ← H.equal_span]; exact h
    exact (not_lt_of_ge (le_refl 0) hz).elim -- zero_le_zero?
  have hs (i):0≤u i:=by unfold u Article.usury; split <;> positivity
  have hL(i) : u i ≤ ‖(y i.1).part i.2.val‖:= by unfold u Article.usury; split; rfl; exact norm_nonneg _
  let f i:=Poly.toll w (r i)*t i
  have hF i : 0≤f i:= mul_nonneg (Poly.worth hw _).le (hx _ _).1
  have hit:Hit Z p.B f b c := by
    intro x
    let bC (i : Article.Key ι R):= Poly.toll w i.2.val*u i
    have hb i :0≤bC i:= mul_nonneg (Poly.worth hw _).le (hs _)
    have hf i : f (e i)=bC i:= by
      unfold f r; rw [he i]; change Poly.toll w ((D.impression a slot).marks _ (Extra.Trajectories.pin i))*u i=bC i;rw [D.marked_pin]
    let exp (a:Support n):=Real.exp (b*coverNumber p.B a)
    let F i:= if x∈Z i then f i*exp (Z i) else 0
    change SumBudget F c
    refine Pad.absolute e hi (u:=F ∘ e) (fun s=>rfl) (fun i hI=>?_ ) ?_
    · by_contra c; apply hI; unfold F f; rw [hneg i c]; split <;> simp
    refine budget_fiberwise (W:=fun i=>if x∈D.span i then Poly.price w (y i)*Real.exp (b*coverNumber p.B (D.span i)) else 0) Prod.fst (fun i=>?_ ) ?_ (h x)
    · unfold F comp; dsimp only; split; exact mul_nonneg (hF _) (Real.exp_pos _).le; rfl
    intro i s hi'
    have hZ j (hj:j∈s): Z (e j)=D.span i := (H.equal_span _).symm.trans (congrArg _ (hi' j hj))
    split
    next hX=>
      let q (i': R.Mode):=Poly.toll w i'*‖(y i).part i'‖ *exp (D.span i)
      have hQ i':0≤q i':=mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (Real.exp_pos _).le
      rw [Poly.price,sum_mul]
      refine (le_trans (b:=∑ j∈s.image (fun i=>i.2.val),q j) ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>hQ _)))
      rw [sum_image (fun j (hj:j∈s) k (hk:k∈s) (h:j.2.val=k.2.val)=>Prod.ext ((hi' j hj).trans (hi' k hk).symm) (Subtype.ext h))]
      apply Finset.sum_le_sum; intro j hj
      unfold F comp; dsimp only; rw [hZ j hj,hf j,if_pos hX]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; unfold bC; rw [←hi' j hj]; exact mul_le_mul_of_nonneg_left (hL j) (Poly.worth hw _).le
    next ht=>
      refine le_of_eq (sum_eq_zero (fun j hj=>?_)); unfold F comp; dsimp only; rw [hZ _ hj, if_neg ht]
  refine ⟨hl,hit,fun v=>budget_mono (hit (ζ v)) (per_nn (fun i=>(hw i).le) (fun i=>(hx _ _).1) · _) (fun i=>?_)⟩
  unfold per expense; rcases eq_or_ne (t i) 0 with H|H
  · rw [H]; simp; split; exact mul_nonneg (hF _) (Real.exp_pos _).le; rfl
  split
  next hv=> rw [if_pos ((hl i.1 i.2).2 1|>.2 (lt_of_le_of_ne (hx i.1 i.2).1 (Ne.symm H)) v hv)]; unfold f; apply le_of_eq; ring
  split; exact mul_nonneg (hF _) (Real.exp_pos _).le; rfl
end YM.RG3.Script.Reserve
