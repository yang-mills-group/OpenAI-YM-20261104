import YM.XSpace.Harmonic
import YM.XSpace.ImageSum

/-!
# Power gain on the inversion image even through high engineering-weight tests

Not a sharp estimate. Avoid punctured-torus Fourier quadrature / even seam widths
here. Projection implies `∑row P² ≤ 1`. Propagate maxima of massless kernels over
*every* intervening shell via discrete harmonicity, count one site per shell. Gains a
half inverse period power in the regime needed for kvlead.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Harmonic
open Function Filter Set Finset Exterior Matrix Lattice Bare Top
open scoped Topology BigOperators
variable {n : Side} {R : Period}

private def MeanAt (o : Site n) (f : Site n → ℝ):= ∀ x, 2< separation x o →
    (∑ i: Axis, (f x-f (x+step i)+(f x-f (x-step i))))=0
private lemma neg_mean {o : Site n} (f : Site n → ℝ) (h : MeanAt o f): MeanAt o (-f):= by
  rintro x hx; specialize h x hx
  let M (g : Site n → ℝ) (i : Axis) := g x-g (x+step i) + (g x-g (x-step i))
  change ∑ i,M f i=0 at h
  change ∑ i,M (-f) i=0; rw [show (∑ i,M (-f) i)= -(∑ i,M f i) by rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _=> by unfold M; simp only [Pi.neg_apply]; abel,h,neg_zero]
private lemma range_for {x o : Site n} {m : ℕ} (h : m<separation x o) (i : Axis): m ≤ separation (x+step i) o ∧ m≤separation (x-step i) o:=by
  have ht:= separation_triangle x (x+step i) o; have hp:= Work.E01.sep_step_le x i; have hh:=separation_triangle x (x-step i) o
  have hv:= Work.E01.sep_step_le (x-step i) i; rw [sub_add_cancel, separation_comm] at hv; omega
private lemma constant_above {o : Site n} {m : ℕ} (f : Site n → ℝ) (hm : 2 ≤ m) (M : ℝ)
    (h : MeanAt o f) (H : ∀ x, m ≤ separation x o → f x ≤ M) (x : Site n) (hx : f x=M) (ht : m< separation x o) (i : Axis) :
    f (x+step i)=M∧f (x-step i)=M:=by
  have he := h x (lt_of_le_of_lt hm ht); simp_rw [hx] at he
  have hg (i : Axis) := H _ (range_for ht i).1; have hh (i : Axis) := H _ (range_for ht i).2
  have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => add_nonneg (sub_nonneg.mpr (hg i)) (sub_nonneg.mpr (hh i)))).mp he i (Finset.mem_univ i)
  constructor <;> linarith [hh i,hg i]
private lemma peaks (o x : R.Sites) {m : ℕ} (f : R.Sites→ℝ) (h : MeanAt o f) (hm : 2≤m) (hp : m ≤ separation x o): ∃ y, separation y o=m ∧ f x ≤ f y:=by
  let D := Finset.univ.filter fun i:R.Sites => m ≤ separation i o
  have hk (i : R.Sites) : i∈D ↔ m ≤ separation i o:= by unfold D; simp
  obtain ⟨z,hz,H⟩:= Finset.exists_max_image D f ⟨x,(hk x).2 hp⟩
  obtain ⟨w,hw⟩:= R.exists_walk z o
  have he (w : Walk) (y : R.Sites) (hw : stop y w=o) (hg : m≤separation y o) (hi : f y=f z):∃ y, separation y o=m∧f x ≤ f y:=by
    induction w generalizing y with
    | nil => change y=o at hw; rw [hw,separation_self] at hg; omega
    | cons d w ih =>
      obtain hp'|hp':= lt_or_eq_of_le hg
      · have hs:= range_for hp' d.dir
        have hb:=constant_above f hm (f z) h (fun x hx=> H x ((hk x).2 hx)) y hi hp' d.dir
        change stop (y+d.vec) w=o at hw
        apply ih (y+d.vec) hw
        · unfold Step.vec; split
          · rw [← sub_eq_add_neg]; exact hs.2
          exact hs.1
        unfold Step.vec; split
        · rw [← sub_eq_add_neg]; exact hb.2
        exact hb.1
      refine ⟨y,hp'.symm, hi.symm ▸ (H x ((hk x).2 hp))⟩
  exact he w z hw ((hk z).1 hz) rfl
private lemma exists_price (o x : R.Sites) {m : ℕ} (f : R.Sites→ℝ) (h : MeanAt o f) (hm : 2≤m) (hp : m ≤ separation x o): ∃ y, separation y o=m ∧ f x^2 ≤ f y^2:=by
  by_cases H : f x<0
  · obtain ⟨y,he,hg⟩:= peaks o x (-f) (neg_mean f h) hm hp; refine ⟨y,he,?_⟩; rw [Pi.neg_apply,Pi.neg_apply] at hg; nlinarith
  obtain ⟨y,he,hg⟩:= peaks o x f h hm hp; exact ⟨y,he,by nlinarith⟩

lemma rowsquare (x : Body 2 n): (∑ y,Top.projector n y x ^2) ≤ 1:=by
  obtain ⟨w,hw⟩:=(Top.projection n).2.1; have ht:= (Top.projection n).2.2
  let P:= Top.projector n
  have h:P*P=P:= calc _=P*(Exterior.d 1 n*w):=by change Top.projector n * P=_; rw [show Exterior.d 1 n*w=P from hw.symm]
                       _ =P:=by rw [← Matrix.mul_assoc]; exact Eq.trans (congr_arg (·*w) ht) hw.symm
  have hi : ∑ y,P y x^2=P x x:= by
    apply Eq.trans _ (congr_fun (congr_fun h x) x); rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _=> by rw [show P x i=P i x from congr_fun (congr_fun (Top.projection n).1 i) x]; ring
  change ∑ y,P y x^2 ≤ 1
  have hh := Finset.single_le_sum (f:=fun i => P i x ^2) (fun _ _=> sq_nonneg _) (Finset.mem_univ x); rw [hi] at hh ⊢; nlinarith
lemma entry_cap (x y : Body 2 n): |Top.projector n x y| ≤ 1:= by
  have ht:= (Finset.single_le_sum (f:=fun i=> Top.projector n i y^2) (fun _ _=> sq_nonneg _) (Finset.mem_univ x)).trans (rowsquare y)
  rw [abs_le]; constructor <;> nlinarith

/-- Power gain for entries of the actual *periodic* Wilson curl covariance.
No smearing or cancellations of signs assumed. -/
lemma image_gain (R : Period) (x : R.Sites) (a : TypeFace 2) (y : Body 2 R.side) (m : ℕ) (hm : m+1 ≤ separation x y.1):
    m*(Top.projector R.side (x,a) y)^2 ≤ 1 := by
  let f : R.Sites → ℝ:= fun x => Top.projector R.side (x,a) y
  have he : ∀ i : Fin m,∃ x' : R.Sites, separation x' y.1=i.val+2 ∧ f x^2 ≤ f x'^2:= fun i=> exists_price y.1 x f (fun z hz=> harmonic_point R.side z a y hz) (by omega) (by omega)
  choose s hS ht using he
  have hh:Injective (fun i:Fin m=>(s i,a)):= by
    intro i j h; have hi : separation (s i) y.1=separation (s j) y.1:= by rw [← show s i=s j from congr_arg Prod.fst h] 
    rw [hS,hS] at hi; exact Fin.ext (by omega)
  calc
    _ = ∑ _i:Fin m,f x^2 :=by simp [f]
    _ ≤ ∑ i : Fin m,f (s i)^2 := Finset.sum_le_sum (fun i _=> ht i)
    _ ≤ ∑ i : Body 2 R.side,Top.projector R.side i y^2 := by
      let T : Fin m → Body 2 R.side:=fun i=>(s i,a); calc
        _ = ∑ i∈Finset.univ.image T, Top.projector R.side i y^2:=by rw [Finset.sum_image (by intros i _ j _ hx; exact hh hx)]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=> sq_nonneg _)
    _ ≤ 1 := rowsquare _

variable {G : Gauge}
lemma cap (p q : Faces n) (a b : G.ColorIndex): |direct p q a b| ≤ 1:= by rw [direct_at]; split; apply entry_cap; simp
lemma decay (R : Period) (p q : Faces R.side) (a b : G.ColorIndex) (m : ℕ) (h : m+1 ≤ separation p.1 (R.reflectedFace q).1) :
    m*(Bare.image (R:=R) p q a b)^2 ≤ 1:=by rw [Bare.image,direct_at]; split; exact image_gain R p.1 (plaquette p.2) _ _ h; simp
end YM.XSpace.Harmonic
