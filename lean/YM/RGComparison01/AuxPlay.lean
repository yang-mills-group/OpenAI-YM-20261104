import YM.RGComparison01.AuxStage

/-! # Rescaled analytic algebra. Actual coefficients and errors from same evaluations. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxStage
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure RG Gauge
open Input Precision Tree Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain PhysicalNext.Repeat WilsonStartup Tensor
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : E→ℝ} {x : E} {C v d h u p : ℝ} {k j n : ℕ} {F G : Co E}

namespace Points

-- product tails entirely finite
lemma multiply (H : Points v d h k j f x F) (H' : Points u d h k j g x G) (hh : 0 ≤ h) (hV : h ≤ 1) : Points (fuse k j v u) d h k j (f*g) x (weave F G):= by
  let P:=price F h k; let Q:=price G h k; let W:=price (weave F G) h k; let s:= Finset.range (k+1)
  let R:=s ×ˢ s; let T:= R.filter fun i=> k < i.1+i.2; let A:=R\T
  let f' (q:ℕ×ℕ) (x:E):= headAt F h q.1 x*headAt G h q.2 x
  have ha:A ⊆ R:= Finset.sdiff_subset
  have hT:T ⊆ R:=Finset.filter_subset ..
  have hz x : W x = ∑ i∈A,f' i x:= by
    let K (_:ℕ):=s
    let I:= s.sigma fun i=> Finset.range (i+1)
    let M (i:Σ _ : ℕ,ℕ) := (i.2,i.1-i.2)
    have hi (l) (hl:l∈I) : l.2≤ l.1 ∧ l.1 ≤ k:= by obtain ⟨hy,hq⟩:= Finset.mem_sigma.mp hl; exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hq), Nat.le_of_lt_succ (Finset.mem_range.mp hy)⟩
    have hm(q:ℕ×ℕ): q∈ A ↔ q∈R ∧ q.1+q.2 ≤ k:= by simp only [A,T,Finset.mem_sdiff, Finset.mem_filter,not_and, not_lt]; tauto
    have hu z' (hl:z'∈s): headAt (weave F G) h z' x=∑ l∈Finset.range (z'+1),f' (M ⟨z',l⟩) x:= by
      unfold headAt weave; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l hl=>?_); have he:= Finset.mem_range.mp hl
      unfold f' M headAt; dsimp only; nth_rw 1 [show z'=l+(z'-l) by omega]; rw [pow_add]; ring
    change (∑ i∈s,headAt _ _ i x)=_
    rw [Finset.sum_congr rfl hu]
    change (∑ z'∈s,∑ l∈Finset.range (z'+1),(fun i:(Σ _:ℕ,ℕ)=>f' (M i) x) ⟨z',l⟩)=_
    apply (Finset.sum_sigma (s:=s) (t:=fun i=> Finset.range (i+1)) (f:=fun i:(Σ _:ℕ,ℕ)=>f' (M i) x)).symm.trans
    refine Finset.sum_bij (fun z _=> M z) (fun z hz=>?_ ) (fun z hz u hv h=>?_) (fun z hz=>?_) (fun _ _=>rfl)
    · obtain ⟨h₁,h₂⟩:=hi z hz; apply (hm _).2; unfold R M s; simp only [Finset.mem_product, Finset.mem_range]; omega
    · rcases z with ⟨z,l⟩; rcases u with ⟨u,v⟩; obtain ⟨ha,hb⟩:=hi _ hz; obtain ⟨hc,hd⟩:=hi _ hv
      unfold M at h; simp only [Prod.mk.injEq] at h; dsimp only at ha hb hc hd; congr 1 <;> omega
    · obtain ⟨ha,hb⟩:= (hm z).1 hz; refine ⟨⟨z.1+z.2,z.1⟩,Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hb),Finset.mem_range.mpr (show z.1<z.1+z.2+1 by omega)⟩,?_⟩; simp [M]
  have he x: (f*g-W) x=(f x-P x)*g x+P x*(g x-Q x)+∑ i∈T,f' i x:= by
    have hx : W x+∑ i∈T,f' i x=P x*Q x:= by rw [hz,Finset.sum_sdiff hT]; unfold R P Q price; rw [Finset.sum_product]; simp_rw [Finset.sum_mul,Finset.mul_sum]; rfl
    simp only [Pi.sub_apply,Pi.mul_apply]; linarith only [hx]
  have hv:= H.nonneg; have hu:= H'.nonneg
  let p1:= v*(u+allowance u k)*2^j
  let p2:= allowance v k*u*2^j
  let p3:=v*u*2^j; let B:=((k+1:ℕ)^2:ℕ)*p3
  have hb : 0 ≤ p3:=by unfold p3; positivity
  have Hp : fuse k j v u=cores k j v u+(p1+p2+B):= by unfold fuse p1 p2 B p3; ring
  rw [Hp]
  have hz : 0 ≤ p1+p2+B:= by unfold p1 p2 B allowance; positivity
  refine ⟨fun i hi=> (bill_joint H H' hh i hi).climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hz) (pow_nonneg hh _)) le_rfl,?_⟩
  have ht i (hi:i∈T): Brush j (p3*h^(k+1)) d (f' i) x:= by
    obtain ⟨he,hv⟩:=Finset.mem_filter.mp hi
    obtain ⟨hc,hd⟩:=Finset.mem_product.mp he
    have hg:=together (H.bill _ (Nat.le_of_lt_succ (Finset.mem_range.mp hc))) (H'.bill _ (Nat.le_of_lt_succ (Finset.mem_range.mp hd)))
    apply hg.climb _ le_rfl; exact (show _= p3*h^(i.1+i.2) from (by rw [pow_add]; unfold p3; ring)).trans_le (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh hV hv) hb)
  have hr:= together H.tail (H'.full hh hV); have hq:= together (H.bulk hh hV) H'.tail
  refine (((hr.gathering hq).gathering (Brush.spree _ _ _ H.pos ht)).climb ?_ le_rfl).shimmy (Eventually.of_forall he)
  rw [Finset.sum_const,nsmul_eq_mul,show v * h^(k+1)*(u+allowance u k)*2^j + allowance v k * (u*h^(k+1))*2^j=(p1+p2)*h^(k+1) by unfold p1 p2; ring]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by unfold cores; positivity)) (pow_nonneg hh _)); rw [add_mul (p1+p2) B]; apply add_le_add_right
  have Hv : T.card ≤ (k+1)^2:= (Finset.card_le_card hT).trans_eq (by rw [Finset.card_product]; simp [s,pow_two])
  unfold B; rw [mul_assoc (↑((k+1:ℕ)^2):ℝ) p3 (h^(k+1))]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr Hv) (mul_nonneg hb (pow_nonneg hh _))

def powPoly (F : Co E) : ℕ → Co E
  | 0 => scalar 1
  | n+1 => weave (powPoly F n) F
def powFee (v : ℝ) (k j : ℕ) : ℕ→ℝ
  | 0 => 1
  | n+1 => fuse k j (powFee v k j n) v
lemma plaster (H : Points v d h k j f x F) (hh : 0≤h) (hp : h≤1) (n:ℕ) : Points (powFee v k j n) d h k j (fun i=> f i^n) x (powPoly F n):= by
  induction n with
  | zero=> simpa only [pow_zero,powFee,powPoly,norm_one] using! start 1 H.pos hh
  | succ n ih=> simp only [pow_succ]; exact multiply ih H hh hp

end Points

-- univariate Taylor for ordinary (nonrepresentational) smooth reset in these estimates
variable (g' : ℝ→ℝ) (p : ℝ)
def point_co (i:ℕ) := Tensor.diagonal (Tensor.coeff g' i 0) (1:ℝ)
lemma dom (x:ℝ) (k : ℕ) : blockTaylor k g' x= ∑ i∈Finset.range (k+1), point_co g' i*x^i:= by
  rw [blockTaylor,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (point_co g' i)]; simpa only [point_co,smul_eq_mul,mul_one] using! Tensor.homogeneous (Tensor.coeff g' i 0) 1 x
open Points

def pacify (g' : ℝ→ℝ) (c:Co E) (p : ℝ) (k : ℕ): Co E :=
    ∑ i∈Finset.range (k+1), point_co (fun t=> g' (t+p)) i • powPoly (c+scalar (-p)) i
def inter (v p : ℝ) (k : ℕ) := v+allowance v k+p
def label (g' : ℝ→ℝ) (C v p : ℝ) (k j : ℕ) := let s := inter v 2 k
    (j.factorial*(C*s^(k+1)))*2^j+∑ i∈Finset.range (k+1),|point_co (fun t=> g' (t+p)) i| * powFee (v+|p|) k j i
lemma attend (H : Points v d h k j f x F) (hh : 0 < h) (hp : h ≤ 1) (hz : F 0=fun _=> p)
    (hi : inter v 2 k*h ≤ 1) (he : ∀ y∈ball (0:ℝ) (inter v 2 k*h), Brush n C 1 (fun t=> g' (t+p)) y) (hj : j ≤ n) (hk : k < n) :
    Points (label g' C v p k j) d h k j (g' ∘ f) x (pacify g' F p k):= by
  let c:= p; let g (t:ℝ):= g' (t+p); let f₁ x:= f x-p
  let F₁:=F+scalar (-p); let B:=powFee (v+|p|) k j
  let u i:=point_co g i; let E' y:=blockTaylor k g (f₁ y)
  have hv:= H.nonneg; let r:= allowance v k; have hr : 0 ≤ r:=by unfold r allowance; positivity
  let s:=inter v 2 k; have hs :0 < s:= by change 0<v+r+2; linarith
  let δ:=v+r+1; have hd: δ*h < s*h:=mul_lt_mul_of_pos_right (by unfold δ s inter r; linarith) hh; have hy : 0<δ*h:= mul_pos (by unfold δ; linarith) hh
  have hC:= (he 0 (mem_ball_self (hy.trans hd))).nonneg
  have ha : Points (∑ i∈Finset.range (k+1), |u i| * B i) d h k j E' x (pacify g' F p k) := by
    have ht : Points (v+|p|) d h k j f₁ x F₁:= by
      have hb:=H.add (start (x:=x) (-p) H.pos hh.le); rw [norm_neg] at hb; exact hb.adjust (Eventually.of_forall (fun i=> sub_eq_add_neg (f i) p))
    let T (i:ℕ) (x:E):=u i*(f₁ x)^i
    have he(i:ℕ): Points (|u i| * B i) d h k j (T i) x (u i • powPoly F₁ i):= (plaster ht hh.le hp i).scale (u i)
    exact (summing _ _ T _ H.pos hh.le (fun i _=> he i)).adjust (Eventually.of_forall (fun i=> by unfold E'; rw [dom,Finset.sum_apply]))
  have ht := H.off_one hz hh.le hp; have h':= ht.climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hh.le) le_rfl
  apply ha.quote ((j.factorial*(C*s^(k+1)))*2^j) _ (by positivity) hh.le
  have hp:Brush j (δ*h) d f₁ x:= h'
  have hx := AuxCurtain.reprice_exp hp hy hd hi he hj hk
  have hB(x:E): g' (f x)=g (f₁ x):= by unfold g f₁; rw [sub_add_cancel]
  refine (hx.climb (le_of_eq ?_) le_rfl).shimmy (Eventually.of_forall (fun i=> congr_arg (· - E' i) (hB i)))
  rw [mul_pow]; ring

section currency
variable {u v : ℝ→ℝ} {G : Gauge} {L : Side}
lemma wages (h : Geo G L u) (k : ℕ): Geo G L (fun t=> allowance (u t) k):= (Geo.fixed _).times h
lemma fusion_geo (k j : ℕ) (h : Geo G L u) (p : Geo G L v) : Geo G L (fun i=> fuse k j (u i) (v i)):= by
  have hp:= (h.times p).times (Geo.fixed (2^j))
  exact ((((Geo.fixed _).times hp).joins ((Geo.fixed _).times hp)).joins (((h.times (p.joins (wages p k)))).times (Geo.fixed _))).joins (((wages h k).times p).times (Geo.fixed _))
lemma pow_geo (h : Geo G L u) (i k j:ℕ): Geo G L (fun t=> powFee (u t) k j i):= by
  induction i with
  | zero=> exact Geo.fixed _
  | succ i ih=> exact fusion_geo _ _ ih h
lemma label_geo (h : Geo G L u) (c C : ℝ) (k j : ℕ): Geo G L (fun t=> label g' C (u t) c k j):= by
  have hv:= ((h.joins (wages h k)).joins (Geo.fixed (2:ℝ))).power (k+1)
  let p (i:ℕ):ℝ:= |point_co (fun t=> g' (t+c)) i|
  exact (((Geo.fixed _).times ((Geo.fixed _).times hv)).times (Geo.fixed _)).joins
    (Geo.expel (Finset.range (k+1)) (fun i t=>p i*powFee (u t+|c|) k j i) (fun i _=> (Geo.fixed _).times (pow_geo (h.joins (Geo.fixed |c|)) i k j)))
end currency
end YM.RGComparison01.AuxStage
