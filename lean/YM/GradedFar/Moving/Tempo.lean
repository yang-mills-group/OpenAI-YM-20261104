import YM.GradedFar.Moving.Snow

/-!
# Apply the same (signed) calibration at the resulting frame and read the step θ
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open private enlarged from YM.GradedFar.Moving.Direction
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ i,z i∈Growth.Small) {simple : G.Simple}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
local notation "s"=> fun i=> resize (r i) (z i)

section all
variable {Z : Rolled G d} (hZ : Righted Z) {F : Pose.Plans G d}
variable (h : Beginning N θ d F) (Y : ℝ → Prediction G d) (hy : Held N Y F) (he : refit Z F)
variable {K : Set (Points n)} (x : I→Points n) (hK : IsCompact K) (hx : K⊆conf n) (hh : ∀ᶠ i in T,x i∈K)
include h H hr hz ht he hZ hy hK hx hh
-- repetition hom_trial now true W-result (all callers)
lemma switched (u : Tags G d n) :
    Pays T (fun i=> F (s i) n (x i) u) (fun i=> tells (Pose.line N (x i) u)) (g∘r) p (fun i=> bend N M (z i) p (θ (r i):ℂ)) := by
    have hb := Eventually.of_forall (f:=T) hz
    obtain ⟨S',hc,hp,hf⟩:= enlarged T N M r z hr hb H θ x hK hx hh h
    have hv := titles T (g ∘ r) _ ((shrink simple).comp hr) (measuring T N M r hr H θ ht) _
      (A:=fun i=> fxt (Pose.Bbook N d) (exp (z i) • x i)) (fun i=>forwards Z (r i) (z i)) u (F:=fun i=> F (r i) n (exp (z i) • x i))
      (covered T N M r z hr hz H hZ θ ht h Y hy he (p:=p)) (fun v=> born T N M r hr H θ _ hc hp hf h v)
    have h1 := beauty (p:=p) T N M r hr H x hK hx hh u
    have hz' := recrop_substitution T (measuring T N M r hr H θ ht) ((shrink simple).comp hr) (psi_lin T N M r z hb H) (fun i=>(tendsK N M H _).start) h1
    refine ⟨h1,(hv.2.sub hz').congr' ?_ (EventuallyEq.refl ..)⟩
    filter_upwards [hr.eventually self_mem_nhdsWithin,hh] with i (hr:r i∈Ioi 0) hi
    let a : Stage n:= ⟨x i,hx hi⟩; let k:= z i
    have HZ : shop (status (train N M d k) (fxt (Pose.Bbook N d) (exp k • x i))) u=(Pose.line N (x i) u).subst (ψ (-k)) := by
      rw [show exp k • x i=(Facets.posing (-k) a).val from (by unfold Facets.posing; dsimp; rw [neg_neg]), Jury.exactC, train_exact N M H, shop, Reg.Point.moves _ _ ((tendsK N M H _).start)]
      rw [show Pose.line N (x i) u=shop (Pose.Bbook N d n a) u by unfold Pose.line shop Reg.Point.story; rw [show x i=a.val from rfl,Jury.exactC]]
    let b:= θ (r i); let R:= F (s i) n (x i) u; let y:=Pose.line N (x i) u; let Y:=F (r i) n (exp k • x i) (forwards Z (r i) k ∘ u)
    have hx := he _ k hr (hz i) n u _ (hx hi)
    change Y - blend _ _ _ - _ = R-_
    rw [show R=Y from hx,HZ,composition_tells _ _ (tendsK N M H _|>.start)]
    unfold bend; abel
end all

lemma addition {X X' : I→ℂ} {Y Y' : I→PowerSeries ℂ} {L : I→ℝ} {t : I→ℂ} (h : Pays T X (fun i=>tells (Y i)) L p t) (h' : Pays T X' (fun i=>tells (Y' i)) L p t) :
    Pays T (fun i=>X i+X' i) (fun i=>tells (Y i+Y' i)) L p t := by
    refine ⟨fun j hj=>?_,?_⟩
    · unfold tells; simp_rw [map_add]; exact (h.1 j hj).add (h'.1 j hj)
    refine (h.2.add h'.2).congr_left (fun i=>?_) ; dsimp only; unfold blend tells; simp_rw [map_add,smul_add,Finset.sum_add_distrib]; abel
lemma subtraction {X X' : I→ℂ} {Y Y' : I→PowerSeries ℂ} {L : I→ℝ} {t : I→ℂ} (h : Pays T X (fun i=>tells (Y i)) L p t) (h' : Pays T X' (fun i=>tells (Y' i)) L p t) :
    Pays T (fun i=>X i-X' i) (fun i=>tells (Y i-Y' i)) L p t := by
    refine ⟨fun j hj=>?_,?_⟩
    · unfold tells; simp_rw [map_sub]; exact (h.1 j hj).sub (h'.1 j hj)
    refine (h.2.sub h'.2).congr_left (fun i=>?_) ; dsimp only; unfold blend tells; simp_rw [map_sub,smul_sub,Finset.sum_sub_distrib]; abel
lemma mult {X X' : I→ℂ} {Y Y' : I→PowerSeries ℂ} {L : I→ℝ} {t : I→ℂ} (hT:Buys T t L 1) (hg:Tendsto L T (𝓝 0)) (h : Pays T X (fun i=>tells (Y i)) L p t) (h' : Pays T X' (fun i=>tells (Y' i)) L p t) :
    Pays T (fun i=>X i*X' i) (fun i=>tells (Y i*Y' i)) L p t := by simp_rw [revenue_tells]; exact Pays.joint T hT hg h h'
variable {Z : Rolled G 6} (hZ : Righted Z) {F : Pose.Plans G 6}
variable (h : Beginning N θ 6 F) (Y : ℝ → Prediction G 6) (hy : Held N Y F) (he : refit Z F)
open XSpace.Rose
local notation "Q"=>Rose.test N.criterion
include h H hr hz ht he hZ hy
lemma full_log (x : I→Points 3) (hx : ∀ᶠ i in T, x i ∈ tsupport Q) :
    Buys T (fun i=> Pose.value (Pose.watchRose F (s i) (x i)) -
      crop p (new_clock N M θ (z i) (r i) p) (Select.Single (Pose.Bbook N 6) (x i))) (g∘r) (p+1) := by
  let t' i:= bend N M (z i) p (θ (r i):ℂ)
  let P i:= batchT (fxt (Pose.Bbook N 6) (x i)); let U (b:Badge) i:= Pose.watchRose F (s i) (x i) b
  have H' (b : Badge) : Pays T (U b) (fun i=> tells (P i b)) (g∘r) p t' :=
    switched T N M r z hr hz H θ ht hZ h Y hy he _ (Rose.test N.criterion).hasCompactSupport (Rose.test N.criterion).tsupport_subset hx (missing (tag G) b)
  have hf:=flux T N M r z hr (Eventually.of_forall hz) H θ ht p
  have hg:= (shrink simple).comp hr
  have H2 := addition T (addition T (mult T hf hg (H' {0,1}) (H' {2})) (mult T hf hg (H' {0,2}) (H' {1})))
    (mult T hf hg (H' {1,2}) (H' {0})); have X:= mult T hf hg (mult T hf hg (H' {0}) (H' {1})) (H' {2})
  have H3 := addition T (subtraction T (H' Finset.univ) H2) (addition T X X)
  simp_rw [new_clock,crop_by,bend_real N M H,Pose.value, Select.Single, b3, two_smul,two_mul]
  exact H3.2

omit h he ht hr hz hZ hy in
private lemma posed (q : ℕ) (hQ : 1 ≤ q) (r : ℝ) :
    (Rose.test N.criterion).applyTo (fun x=> crop q r (Select.Single (Pose.Bbook N 6) x))=
      (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*(r:ℂ) := by
  simp only [crop_eq]; rw [Read.smear_sum]
  · simp_rw [Read.smear_one, Pose.registered N M H]; rw [Finset.sum_eq_single 1]; · simp [mul_comm (r:ℂ)]
    · intro b hb h; simp [coeff_X, h]
    intro h; simp at h; omega
  intro i _; exact ((Select.steady _ (Pose.birth N M H 6).1).const_mul _).mono (Rose.test N.criterion).tsupport_subset

/-- Execute the B-clock in the step. Result is **with θ fixed**. -/
lemma time_value (hθ : θ = Pose.kinetic N F) (hp : 1≤p) : Buys T (fun i=> (θ (s i):ℂ) -
    bend N M (z i) p (θ (r i):ℂ)) (g∘r) (p+1) := by
  let c:=cT N.criterion.cut G N.criterion.image; let t':=fun i=> new_clock N M θ (z i) (r i) p
  let q:=tsupport Q; let S:= I × ↥q; let f (i:S):=i.1; let x (i:S):=i.2.val
  let A:= comap f T
  obtain ⟨C,hC,hv⟩:= (full_log A N M (r∘f) (z∘f) (hr.comp tendsto_comap) (fun i=>hz i.1) H θ ht hZ h Y hy he x
    (p:=p) (Eventually.of_forall fun i=>i.2.property)).exists_pos
  have hc : 0< |c| :=abs_pos.mpr N.criterion.fresh.ne; apply IsBigO.of_bound (Read.Value Q*C/|c|)
  filter_upwards [eventually_comap.mp hv.bound,(span_nears T N M r z hr (Eventually.of_forall hz) H).eventually self_mem_nhdsWithin] with i hX (hr : s i∈Ioi 0)
  let A x:=F (s i) 3 x; let F' x:= Pose.watchRose F (s i) x
  let B x:=crop p (t' i) (Select.Single (Pose.Bbook N 6) x)
  have hb:Tendsto (fun v=>θ v / g v) τ (𝓝 1):=ht
  have hzero (b):ContinuousOn (fun x=> F' x b) q := (hy.cont _ hr 3 _).mono (Rose.test N.criterion).tsupport_subset
  have ha : ContinuousOn (fun x=> Pose.value (F' x)) q := by
    unfold Pose.value; exact ((hzero _).sub ((((hzero _).mul (hzero _)).add ((hzero _).mul (hzero _))).add ((hzero _).mul (hzero _)))).add
      (ContinuousOn.const_mul (((hzero _).mul (hzero _)).mul (hzero _)) _)
  have hb0 : ContinuousOn B q := by
    simp only [B, crop_eq]
    exact continuousOn_finsetSum _ fun j _=> ((Select.steady _ (Pose.birth N M H 6).1).const_mul _).mono (Rose.test N.criterion).tsupport_subset
  let Ψ : ℂ := c * (t' i:ℂ) -- ← coercion
  have hw0 : (Rose.test N.criterion).applyTo B =Ψ := posed N M H p hp (t' i)
  have hx : ‖Pose.total N F (s i)-Ψ‖ ≤ Read.Value Q*(C*‖(g∘r) i^(p+1)‖) := by
    rw [←hw0, Pose.total, ← Read.smear_sub Q ha hb0]; exact Read.value_le _ (ha.sub hb0) (fun j hj=> hX (i,⟨j,hj⟩) rfl)
  have θp : θ (s i)= (Pose.total N F (s i)).re/c := congrFun hθ _
  have e : (Pose.total N F (s i)-Ψ).re=(θ (s i)-t' i)*c := by
    rw [θp,Complex.sub_re, sub_mul, div_mul_cancel₀ _ (abs_pos.mp hc)]; unfold Ψ; rw [← Complex.ofReal_mul,Complex.ofReal_re,mul_comm (t' i) c]
  rw [← bend_real N M H]; -- below need θ untouched
  change ‖(θ (s i):ℂ)-(t' i:ℂ)‖ ≤ _; rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,show Read.Value Q*C/|c| * _=Read.Value Q*(C*‖(g∘r) i^(p+1)‖) / |c| by ring, le_div_iff₀ hc, ←abs_mul,← e]
  exact (Complex.abs_re_le_norm _).trans hx
end
end YM.FVA2.GradedFar.Moving
