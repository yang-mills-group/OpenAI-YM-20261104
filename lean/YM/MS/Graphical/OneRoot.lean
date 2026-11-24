import YM.MS.Graphical.RemovingFactor

/-!
# Price ALL scales of a renormalized bulk or one-pin forest for joining

For example our `Diagram.sectorMark` has a rank cap and satisfies the analytic
and UV hypotheses `Moony/Stay` through its Bob recursion (see `Panels.lean`).
Here pass from MS cost on *pages* to budgets on the *scaled* single component.
The rate permitted for these components in log time is some exponential
(with constants/seminorms for all t bounded above, not necessarily decay).
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I:Type} {a R : ℝ} {G : Gauge} {U : Set ℂ} {Y : I→ℂ} {m k n ℓ : ℕ} {X : Flats G} {q : ℤ}
variable {f : Coat G} {hp : Form0 false (f 0)}

abbrev scaleRun (k ℓ : ℕ) (y : ℝ) (H : Coat G) : Schedule G:= fun t z=> hikeP z k ℓ y t (H z)

lemma onCompact (h : Hol (disc R) f) (hx : IsCompact U) (hp : U⊆ disc R) (hv : ∀ i, Y i ∈ U) :
    fell 0 1 (fun i=> f (Y i)) := by
  cases isEmpty_or_nonempty I with
  | inl h=>
    rw [show (fun i=>f (Y i))=(fun _: I=>0) from funext (fun i=>isEmptyElim i)];
    exact fall_zero fun _=>zero_le_one
  | inr H=>
    obtain ⟨r,hr,hR,ht⟩:= Stir hx ⟨_,hv (Classical.arbitrary I)⟩ hp
    obtain ⟨p,hv',hp⟩:= exists_between hR
    let U:= closedBall (0:ℂ) p
    obtain hX:= h.price _ p (hr.trans_lt hv') (closedBall_subset_ball hp)
    exact fun m E _ _ _ w=> uGrab (hX m E w) (fun i=>(⟨Y i,closedBall_subset_closedBall hv'.le (ht (hv i))⟩:U))

lemma exponent_weak (hf : Hol (disc R) f) (hr : R≤1) (h k : ℕ) (y : ℝ) :
    Subponential R (scaleRun h k y f) := by
  let s :ℝ:= -(h:ℝ)-2*k; let t' : ℝ:=-(h:ℝ)+2*k
  refine ⟨s, fun I t Z B hv K HK hK hz=>?_⟩
  have he : fell 0 1 fun i=> weight (Z i) k y • f (Z i) := by
    have hep: Hol (disc R) (fun z=> weight z k y • f z):= hf.rate (x:=fun z=> weight z k y) (by simp_rw [cubic]; intro; intros; fun_prop);
    exact onCompact hep HK hK hz
  have hc(i:I): |(Z i).re| ≤ 1 := (Complex.abs_re_le_norm _)|>.trans ((mem_ball_zero_iff.mp (hK (hz i))).le.trans hr)
  have hx : scaleC 0 (fun i=> exp (s*t i)) (fun i=> ‖amount (vamp (Z i) h k) (t i)‖) := rate_expense hv
     (Z:=fun i=> vamp (Z i) h k) (by intro i; unfold s; obtain ⟨hH,hX⟩:=abs_le.mp (hc i); simp [vamp,toll]; nlinarith [(Nat.cast_nonneg (α:=ℝ) k)])
     (t:=t') (by intro i; unfold t'; obtain ⟨hH,hX⟩:=abs_le.mp (hc i); simp [vamp,toll]; nlinarith [(Nat.cast_nonneg (α:=ℝ) k)])
  convert! fall_scale he hx using 1
  · ext; simp
  funext i
  unfold scaleRun hikeP; rw [← cert,map_smul, show plow (vamp (Z i) h k) (t i) _= amount (vamp (Z i) h k) (t i) • plow 0 (t i) (f (Z i)) from
    (by rw [← Alps.shift,zero_add]),map_smul,cert,snow,neg_add_cancel,posing,smul_comm]

lemma prorule (hf : Hol (disc R) f) (hp : ∀ i∈disc R, i≠0 →Sturdy false (f i) ∧ Issue q (f i))
    (k ℓ : ℕ) (y : ℝ) (hR : Short R) : PinPrice false R q (scaleRun k ℓ y f) := by
  refine ⟨from_except ?_ hR.1 ?_ ?_, exponent_weak hf hR.2.2 ..⟩
  · intro t; unfold scaleRun; simp_rw [ew]; exact Hol.rate (hf.grazes t _) (x:=fun i=> weight i ℓ (y+t))
       (fun p hp=> by simp_rw [cubic]; fun_prop)
  · intro z hz hn m w
    unfold scaleRun; simp_rw [ew,cubic];
    let U:=f z
    have he:= fun p:ℝ=> s_p_vector U (ray w) 1 p (-(k:ℂ));
    simp_rw [fieldVal, ray_sail] at he; unfold U at he
    simp only [Pi.smul_apply,smul_eq_mul]; refine Continuous.measurable (Continuous.mul (by fun_prop) ?_)
    simp_rw [he]; exact Continuous.mul (by unfold amount; fun_prop)
       (((hf.link hz isOpen_ball m ℝ (ray w)).smooth ()).continuous.comp (f:=fun t:ℝ => exp t • (1:ℝ)) (by fun_prop))
  intro z hz hn t; unfold scaleRun
  obtain ⟨A,h⟩:=hp z hz hn; exact ⟨ fun i=> Limit.smul _ (fun l hl=> by rw [plow,h i _ (by simpa [sr] using hl),mul_zero]), Sturdy_scale (Alps.Stays A ..) _⟩

lemma succPage (h : Rent X n) (hp : Moony false X) (hk : Cap q X) (k ℓ : ℕ) (y : ℝ) :
    Countered false q (fun t=> paid n (scaleRun k ℓ y (X ℓ) t)):= by
  obtain ⟨F,x,R,hR,hx,hV,H⟩:= show Live (paid n (X ℓ)) from h ℓ
  have hv : ∀ᶠ z in dotty, Sturdy false (x z) ∧ Issue q (x z):= by
    filter_upwards [hk ℓ, hp ℓ |>.dice, hV] with i hi hh ht; rw [ht,paid];
    exact ⟨Sturdy_scale hh _, fun j=>Limit.smul _ ((show Issue q (X ℓ i) from hi) j)⟩
  obtain ⟨p,ht,hw⟩:= dotty_mem.mp hv; obtain ⟨T,hT,hP,hQ⟩:= shortening hR ht
  refine ⟨_,_,hT,?_,prorule (hx.mono (ball_subset_ball hP)) (fun i hi he=> hw i (ball_subset_ball hQ hi) he) k ℓ y hT⟩
  apply hV.mono; intro i hi t; change _ = hikeP i k ℓ y t (x i); rw [hi,paid,hike_mul]; rfl

/-- All pages, priced *as assembled* (cannot require this PinPrice of the pole separately).
At log mass = y, still with every scale. -/
theorem mark_prices (h : Moony false X) (hp : Cap q X) (k : ℕ) (he : Stay k X) (y : ℝ) :
    Countered false q fun t=> Parade X k y t := by
  obtain ⟨n,hn⟩:= tallP (Moony.toast h); let u i t:= paid n (scaleRun k i y (X i) t);
  have he' (S:Finset ℕ) : Countered false q (∑ i∈ S,u i):= by
    induction S using Finset.induction with
    | empty=> rw [Finset.sum_empty]; exact Countered.zero' ..
    | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (succPage hn h hp k i y).add ih
  have hx(t:ℝ) : paid n (Parade X k y t)= (∑ i∈X.support, u i) t := by
    rw [Page X.support fun _ he=>he]; simp_rw [paidSum,Finset.sum_apply]; rfl
  apply Countered.unloads (n:=n) ?_ (fun t=> he ..); rw [funext hx]; exact he' X.support
end YM.MS.Graphical
