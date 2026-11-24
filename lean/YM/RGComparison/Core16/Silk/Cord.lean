import YM.RGComparison.Core16.Silk.Skein
/-!
# PT covariance recurrence (FULL Ray & normalized ⟨·⟩vac)

No products of independently conditioned pivots. The operator on words harmonizes
with future price-vector jobs by projection in the cutOff kernel on the M-ν determinant
Fe closure. Deals with Grassmann-free real sensors only, template at identity,
INCLUDING Finer sector tickets as H:Steady. Brush costs for Θ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D L : Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D} (P:Planet X S ι k T)(H:P.Steady) (i:Wire G ι) {p:ContDiffBump (0:ℝ)} (hp:Dust p X.δ)

open Lumen.Gravity

-- Two data types Gear.Jet/Wire; not confuse primitive patch.n with list of all inserted coordinates. Kept contours through qass ticket later. For now single support only measured in configurations.
-- Let clip accumulation at initialized Θ stamp absorb errors at `sight`, not dropping corrections in raw log.
def wingK (R: Rail G ι→Roll) (w:Rail G ι) (i j:Wire G ι) := day (night (guide i) (wing G (scorecard i j)) R w) 0
omit [Fintype ι] in
lemma nap (j:ℕ) (Y:Stuff G ι L) (R: Rail G ι→Roll)(w:Rail G ι): night Y 0 R w j=0 := by
    unfold night tagPrice warpPay YM.Tensor.coeff; apply sum_eq_zero; intro x _; simp
omit [Fintype ι] in
lemma day_zero (u:ℕ):day (0:ℕ→Roll) u=0:=by
    ext n; unfold day dawn shiftFront; simp [nth]
-- correction fove identified absent in germ; true SL history still retains it via Asp
include H hp
lemma invoice (w: Rail G ι):train (sight P w (fove P i p)) 0 ∧ ∀ j:Wire G ι, train (sight P w (belt P i j p)) (wingK (price P) w i j):= by
    obtain ⟨C,hC,h⟩:=Gravity.sky hp H.prices; obtain ⟨hy,hz⟩:= h _ _ _ _ _ _ S P H i
    have he: night (guide i) (wing G none) (price P) w=0:= funext fun i=> nap (L:=Unit) i _ _ _
    constructor
    · have h:=prelude w H hy (wing_smooth _); rw [he, day_zero] at h; exact h
    exact fun j=> prelude w H (hz j) (wing_smooth _)

-- Derivative hits occurrences with multiplicity -- no cut at same type stencil
-- eraseIdx; no cardinality optimizer here.
def windDown (R: Rail G ι→Roll) (i:Wire G ι) (w:Rail G ι):= ∑ k:Fin w.length,wingK R (w.eraseIdx k) i w[k]
def boundary (b:ContDiffBump (0:ℝ))(w:Rail G ι)(g:ℝ) := P.expect g (P.dark b i*depart i g w)

omit H hp [Fintype ι] in
private lemma balance (w:Rail G ι)(g:ℝ): depart i g w= ∑ j:Fin w.length,paper i w[j] * sing (w.eraseIdx j) g:=by
    induction w with
    | nil=> simp [depart]
    | cons a w he=>
       rw [depart,he,_root_.mul_comm (tally g a), Finset.sum_mul]
       let f j:=paper i ((a::w)[(j:Fin (w.length+1)).val]' (by simpa using j.isLt)) * sing ((a::w).eraseIdx j) g
       change _ = ∑ i:Fin (w.length+1), f i
       rw [Fin.sum_univ_succ f]
       congr 1; refine sum_congr rfl (fun j _=>?_); change _ = paper i w[j] * sing (a::w.eraseIdx j) g; ext x; simp only [Pi.mul_apply,sing_cons]; ring

lemma colder (w:Rail G ι) : train (boundary P i p w) (windDown (price P) i w):= by
    let F (j:Fin w.length) := sight P (w.eraseIdx j) (belt P i w[j] p); let D (j:Fin w.length) := wingK (price P) (w.eraseIdx j) i w[j]
    have he(j:Fin w.length): train (F j) (D j):= (invoice P H i hp (w.eraseIdx j)).2 w[j]
    apply (train.join F D univ (fun j _=> he j)).travel
    filter_upwards [Fk.tollLess (willing H.prices)] with g hg
    have hh : ∀ j:Fin w.length, Envelope (P.dark p i*(paper i w[j]*sing (w.eraseIdx j) g)):=fun j => ((P.whirl p i).1.mul ((havenreal (paper_cont ..)).mul (havenreal (sing_cont ..))))
    unfold boundary F sight; rw [balance,mul_sum,paid H hg _ (fun j:Fin w.length=> P.dark p i* (paper i w[j]*sing (w.eraseIdx j) g)) (fun i _=> hh i),Finset.sum_apply]
    refine sum_congr rfl (fun x _=> congr_arg (P.expect g) ?_); unfold belt; ring

def cheaper (a:k)(n:ℕ)(R:Rail G ι→Roll)(w:Rail G ι) := night (path P i a) (recipe X (P.glyph a,P.hint a i.1,i.2)) R w (2+n)

def due (R: Rail G ι→Roll) (w:Rail G ι):= ∑ a∈P.within i.1,day (fun j=> cheaper P i a j R w) 1

def offpay (b:ContDiffBump (0:ℝ))(w:Rail G ι)(g:ℝ) := P.expect g (fun x=> sing w g x*(P.dark b i x* P.attr i g x/g)) -
    (Gravity.tilt P i*P.expect g (sing w g) + ∑ j,P.plank i j * P.expect g (sing (j::w) g))

-- used at arbitrary coarse point within Cone in CP6. Price H still pays `t∈S.Choices ptr∈w`
lemma pays (w:Rail G ι): train (offpay P i p w) (due P i (price P) w):=by
    obtain ⟨C,hC,h⟩:= Gravity.need_cost H.prices; let ψ a:=recipe X (P.glyph a,P.hint a i.1,i.2)
    have h (a) (ha:a∈P.within i.1):= h _ _ _ _ _ _ S P H p hp i a ha; let u a:= hiccup P w (path P i a) (ψ a) (Gravity.weight P i p a)
    refine (train.join u _ _ (fun j hj=> stumble w H (h j hj) ((fatigue H.prices ..).of_le le_top))).travel (Fk.tollLess ?_)
    filter_upwards [willing H.prices] with s hs; change _= Gravity.lamp_gap P i p w s
    rw [taxes i H h s hs w,Finset.sum_apply]; refine sum_congr rfl fun j hj=>?_; unfold u hiccup Lumen.lapse; simp only [pow_one]; unfold sight; rw [div_eq_inv_mul]

-- PT recurrence explicitly logarithm corrected for stencil; available `nth` identity with costs
-- in letter assembly. Not substituting into GoalM via Measure.quota.
def stepLaw (R:Rail G ι → Roll)(w:Rail G ι) := ∑ j,P.plank i j • R (j::w)
def taskBill (R:Rail G ι → Roll) (w:Rail G ι):= windDown R i w - Gravity.tilt P i • R w -due P i R w
omit hp in
lemma settled (w:Rail G ι) : stepLaw P i (price P) w = taskBill P i (price P) w := by
    obtain ⟨b,hb⟩:= buys H.prices.extent.1; let F:=∑ j,P.plank i j • sway P (j::w)
    have h:train F (stepLaw P i (price P) w):=train.join _ _ _ (fun j _=>(supplies _ H).lift _)
    rw [show taskBill P i (price P) w=windDown (price P) i w+0 - Gravity.tilt P i • price P w -due P i (price P) w from ?_]; swap -- parse issue
    · unfold taskBill; rw [add_zero] -- infer ?_
    apply h.unique; refine ((((colder P H i hb w).carries (invoice P H i hb w).1).deduct ((supplies w H).lift _)).deduct (pays P H i hb w)).travel ?_
    filter_upwards [Fk.tollLess (willing H.prices), Tested.eventually_pos] with g hg ht
    unfold F; rw [Pi.sub_apply,Pi.sub_apply,Pi.add_apply,offpay,duty hb i H hg ht w,Finset.sum_apply]; change _-(boundary P i b w g+sight P w (fove P i b) g-(Gravity.tilt P i*sway P w g+_)) = _ -- boundary x lacks g!
    dsimp only [boundary,sight, Pi.smul_apply,sway,smul_eq_mul]; abel
end YM.RGComparison.Core16.Silk
