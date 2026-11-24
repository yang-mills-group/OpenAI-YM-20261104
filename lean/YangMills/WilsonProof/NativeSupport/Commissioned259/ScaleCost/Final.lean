import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Steps
/-! # Earn growing-variant G.1 errors from compact-ratio purchases in this calculation -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {d : ℕ} {D : Route G} (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[𝓝[>] 0] (g0 G))
    {a b : ℝ} (hb : 0 < b) (p n : ℕ)
-- purchase two estimates together at any sufficiently large order
abbrev paired (D : Route G) (B : ℝ→Frames G) (R : ℝ→PowerSeries ℂ) (t : ℝ→ℝ) (p d : ℕ) (s T :ℝ) :=
    ‖(↑(t (s*T)):ℂ)-crop p (t s) (R (-Real.log T))‖ + stiffness (actual D d s T-form B d T p (t s))
private lemma paired_pos (s T : ℝ): 0 ≤ paired D B R t p d s T := add_nonneg (norm_nonneg _) (stiffPos _)
def Balances (D : Route G) : Prop := ∀ (r s T : ℝ) (d : ℕ),
    D r T d = D r s d * D s T d
variable (hD : Balances D)
local notation "g" => g0 G
local notation "late" => 𝓝[>] (0:ℝ)
local notation "bill" => paired D B R t
include hD
private lemma reshet (s T : ℝ) (A : ℝ) (ha : stiffness (actual D d s 2) ≤ A) (hA : 1 ≤ A) :
    bill p d s T ≤ A*bill p d (s*2) (T/2) +
      ‖crop p (t (s*2)) (R (-Real.log (T/2)))-crop p (t s) (R (-Real.log T))‖ +
      stiffness (actual D d s 2 * form B d (T/2) p (t (s*2))-form B d T p (t s)) := by
  let Φ := actual D d s 2; let L := form B d (T/2) p (t (s*2)); let F' := actual D d (s*2) (T/2)
  let K := form B d T p (t s); let Z := crop p (t (s*2)) (R (-Real.log (T/2))); let Y:= (↑(t (s*T)):ℂ)
  let Q := crop p (t s) (R (-Real.log T))
  have eq : s*2*(T/2)=s*T := by ring
  have hs : actual D d s T=Φ*F' := by
    unfold Φ F' actual; rw [composition',eq]; exact congr_arg columns (hD s (s*2) (s*T) d)
  unfold paired; rw [eq,hs]
  have i : stiffness (Φ*F' - K) ≤ A*stiffness (F'-L)+stiffness (Φ*L-K) := by
    rw [show Φ*F'-K=Φ*(F'-L)+(Φ*L-K) by noncomm_ring]; exact (stiffAdd _ _).trans
      (add_le_add (le_trans (stiffMul Φ _) (mul_le_mul_of_nonneg_right ha (stiffPos _))) le_rfl)
  have z : ‖Y-Q‖ ≤ A*‖Y-Z‖+‖Z-Q‖ := by
    rw [show Y-Q=Y-Z+(Z-Q) by abel]
    exact (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_left (norm_nonneg _) hA) le_rfl)
  change ‖Y-Q‖+stiffness _ ≤ A*(‖Y-Z‖+stiffness (F'-L))+_+_
  exact (add_le_add z i).trans_eq (by ring)

variable (S : StepCost G R B t D)
include S hG H ht
include hb
lemma recur (A : ℝ) (hA : 1 ≤ A) (H' : ∀ᶠ s in late, stiffness (actual D d s 2) ≤ A) : ∀ᶠ p : ℕ in atTop,
    ∃ C:ℝ, 0<C ∧ ∀ᶠ r in late, ∀ s T, permit G a b r s T →
      (T ≤ 2 → bill p d s T ≤ C*g r^n) ∧
      (2 ≤ T → bill p d s T ≤ A*bill p d (s*2) (T/2) + C*g r ^n) := by
  -- enough margin with b*d for logs and scales, constants can depend on order
  filter_upwards [eventually_gt_atTop (0:ℕ), tendsto_natCast_atTop_atTop (R:=ℝ)|>.eventually_ge_atTop ((n:ℝ)+b*d)] with i hi hp
  obtain ⟨p,rfl⟩:= Nat.exists_add_one_eq.mpr hi
  have hc (k : ℕ) (h : k ≤ d) : ((p+1+1:ℕ):ℝ)-b*k-1 ≥ n := by
    push_cast at *; nlinarith only [hp, hb,(by exact_mod_cast h : (k:ℝ) ≤ d)]
  -- step case over all poses
  let I := {v : ℝ × ℝ × ℝ // permit G a b v.1 v.2.1 v.2.2 ∧ 2 ≤ v.2.2}
  let r (i:I):=i.val.1; let s (i:I):= i.val.2.1; let T (i:I):=i.val.2.2; let X:=comap r late
  have hT : ∀ᶠ i in X, 2 ≤ T i := Eventually.of_forall fun i=> i.property.2
  have ht : ∀ᶠ i in X, permit G a b (r i) (s i) (T i) := Eventually.of_forall fun i=> i.property.1
  have h' := reports H hG (show t=O[late] g from by assumption) tendsto_comap ht hT (S.clock p) (S.fields d p)
  have hw := (journey hG tendsto_comap ht hT).2
  have hgt := (pace hG).comp (tendsto_comap (f:=r))
  have hC := limit hG tendsto_comap hw
  obtain ⟨K,hK,E⟩ := (permit_price hb hgt (hw.mono fun i h=>h.2.1) hC (p+1+1) 0 n (hc 0 (Nat.zero_le d)) (h'.1.extend (Eventually.of_forall fun i=>by simp))).exists_pos
  obtain ⟨K',hK',W⟩ := (permit_price hb hgt (hw.mono fun i h=>h.2.1) hC (p+1+1) d n (hc d le_rfl) h'.2).exists_pos
  have ep := eventually_comap.mp ((now hgt).and ((E.bound.and W.bound).and ((corridor hG tendsto_comap ht).1.eventually H')))
  let I' := {v : ℝ × ℝ × ℝ // permit G a b v.1 v.2.1 v.2.2 ∧ v.2.2 ≤ 2}
  let r' (i:I'):=i.val.1; let X':=comap r' late
  have hi : ∀ᶠ i in X', permit G a b (r' i) (i.val.2.1) (i.val.2.2) := Eventually.of_forall fun i=> i.property.1
  have y:=corridor hG (s:=fun i:I'=>i.val.2.1) tendsto_comap hi
  have hz := step_cost_aux (hi.mono fun i h=> h.2.1) y.1 (Eventually.of_forall fun (i:I')=> i.property.2)
    (S.clock p) (S.fields d p) hG
  have i' : n ≤ p+1+1 := by have h := hc 0 (Nat.zero_le d); push_cast at h; exact_mod_cast (show (n:ℝ) ≤ p+1+1 by linarith)
  have hv' := (y.2.1.pow (p+1+1)).trans (Fare.over_pow n (p+1+1) i' X' (g ∘ r')
    (((g0_zero hG).comp tendsto_comap |>.abs).eventually (ge_mem_nhds (by simp : |(0:ℝ)|<1))))
  obtain ⟨U,hU,hbase⟩ := ((isBigO_norm_left.mpr (hz.1.trans hv')).add (hz.2.trans hv')).exists_pos
  have ebase := eventually_comap.mp (hbase.bound.and (now ((pace hG).comp (tendsto_comap (f:=r')))))
  refine ⟨max U (K+K'),lt_max_of_lt_left hU,?_⟩; filter_upwards [ep,ebase] with r₀ e hbase' s T h; constructor
  · intro v; obtain ⟨i,j⟩:= hbase' (⟨(r₀,s,T),h,v⟩:I') rfl; change ‖bill (p+1) d s T‖ ≤ U * ‖g r₀ ^ n‖ at i; change 0< g r₀ at j
    rw [ Real.norm_of_nonneg (paired_pos _ ..),Real.norm_of_nonneg (pow_nonneg j.le _) ] at i; exact i.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg j.le _))
  intro v; obtain ⟨j,⟨q,z⟩,y⟩:= e (⟨(r₀,s,T),h,v⟩:I) rfl
  let Z:= stiffness (actual D d s 2*form B d (T/2) (p+1) (t (s*2))-form B d T (p+1) (t s)); let Q :=
      ‖crop (p+1) (t (s*2)) (R (-Real.log (T/2)))-crop (p+1) (t s) (R (-Real.log T))‖
  change ‖Z‖≤K'*‖g r₀^n‖ at z; change Q ≤ K*‖g r₀^n‖ at q; change 0<g r₀ at j
  rw [Real.norm_of_nonneg (show 0 ≤ Z from stiffPos _),Real.norm_of_nonneg (pow_nonneg j.le _)] at z; rw [Real.norm_of_nonneg (pow_nonneg j.le _)] at q
  apply (reshet (p+1) hD s T A y hA).trans
  rw [add_assoc]
  exact add_le_add le_rfl ((add_le_add q z).trans ((by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg j.le _))))

omit hD S hG H ht hb in
private lemma peel {u b r A L : ℝ} {E : ℝ→ℝ→ℝ} (hr : 0<r) (hA : 1 ≤ A) (hL : 0 ≤ L) {p : ℕ} (hp : A+1 ≤ 2^p)
    (e : ∀ s T, permit G u b r s T → (T ≤ 2 → E s T ≤ L) ∧ (2 ≤ T → E s T ≤ A*E (s*2) (T/2)+L)) :
    ∀ s T, permit G u b r s T → E s T ≤ L*T^p := by
  intro s T h
  suffices z : ∀ k : ℕ, ∀ s T, permit G u b r s T → T ≤ k+2 → E s T ≤ L*T^p by exact z ⌈T⌉₊ s T h (by linarith [Nat.le_ceil T])
  intro k; induction k with
  | zero => intro s T h' hk; exact ((e s T h').1 (by simpa using hk)).trans (le_mul_of_one_le_right hL (one_le_pow₀ h'.2.1))
  | succ k ih =>
    intro s T h hk; rcases le_total T 2 with z|z
    · exact ((e s T h).1 z).trans (le_mul_of_one_le_right hL (one_le_pow₀ h.2.1))
    have e' := (e s T h).2 z; have hc := ih (s*2) (T/2) (splits h hr z |>.2) (by push_cast at *; linarith [Nat.cast_nonneg (α:=ℝ) k]); apply e'.trans
    let S : ℝ:= T/2
    have h : 1 ≤ S := by unfold S; linarith
    calc A*E (s*2) (T/2)+L ≤ A*(L*S^p)+L*S^p := add_le_add (mul_le_mul_of_nonneg_left hc (zero_le_one.trans hA)) (le_mul_of_one_le_right hL (one_le_pow₀ h))
         _ = (A+1)*(L*S^p) := by ring
         _ ≤ 2^p*(L*S^p) := mul_le_mul_of_nonneg_right hp (by positivity)
         _ = _ := by rw [mul_left_comm, ← mul_pow,show 2*S=T by unfold S; ring]

/-- Main growing estimates of QScale (physics calculation in the proof) under its
**compact step ratio** hypotheses. Thus need no argument price unbounded in T in advance.
For field availability in M.3 need K cost and inverse from this too. -/
theorem movement (d : ℕ) : ∀ᶠ p : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in late,
    ∀ T ≥ 1, T ≤ a*g r^(-b) → bill p d r T ≤ C*g r^n := by
  obtain ⟨A,hA,amp⟩:= amplifier hG ht (S.clock 0) (S.fields d 0)
  obtain ⟨k,hk⟩:= pow_unbounded_of_one_lt (A+1) (by norm_num : (1:ℝ)<2)
  let N := ⌈b*k + n⌉₊; have nN := Nat.le_ceil (b*k+n)
  filter_upwards [recur (a:=a) H hG ht hb N hD S A hA (show ∀ᶠ s in late, stiffness (actual D d s 2) ≤ A from amp)] with p ⟨L,hL,H⟩
  have u := H.and ((g0_pos hG).and self_mem_nhdsWithin); let I := {x: ℝ×ℝ // permit G a b x.1 x.1 x.2}; let r(i:I):=i.val.1
  let T (i:I):=i.val.2; let X:=comap r late; let M:=g ∘ r; have hi : ∀ᶠ i in X, permit G a b (r i) (r i) (T i) := Eventually.of_forall Subtype.property
  have hg : Tendsto M X late := (pace hG).comp tendsto_comap
  obtain ⟨K,hK,f⟩:= ((show (fun i:I=>M i ^ N*T i^k)=O[X] fun i=>M i ^ (N-b*k) from by rw [show (fun i:I=>M i ^ N*T i^k)=(fun i:I=>M i ^ (N:ℝ)*T i^k) from funext fun _=>by simp]; exact account hg (hi.mono fun i h=>h.2.1) (limit hG tendsto_comap hi) k N).trans (smaller hg (show (n:ℝ) ≤ N-b*k by linarith))).exists_pos
  apply Exists.intro (L*K); refine ⟨by positivity,?_⟩
  simp_rw [Real.rpow_natCast] at f
  have ht:=(eventually_comap.mp f.bound)
  filter_upwards [u,ht] with r ⟨e,i,j⟩ ht T u v
  have hr : 0<r := j
  have h0 : permit G a b r r T := ⟨le_rfl,u,mul_le_mul_of_nonneg_left v hr.le⟩
  have Z := peel hr hA (mul_nonneg hL.le (pow_nonneg i.le _)) hk.le (E:=bill p d) e r T h0
  have w := ht (⟨(r,T),h0⟩:I) rfl; change ‖g r ^ N*T^k‖≤ K*‖g r ^ n‖ at w
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at w; exact Z.trans (by rw [mul_assoc,mul_assoc]; exact mul_le_mul_of_nonneg_left w hL.le )
end YM.FVA2.GradedFar259.ScaleCost
