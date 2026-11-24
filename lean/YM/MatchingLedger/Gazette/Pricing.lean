import YM.MatchingLedger.Gazette.Ports
import YM.Push.STATIONARY_UNIFORM.Prediction
import YM.LocalH.Haar

/-!
# Order/ratio pricing of individual SD vertices

Includes tag equality and honest full costs of paths, faces, Haar. Use the stationary uniform
licenses rather than transferring analyticity radii from extensive coupling log. Continue in
small sup-norm (unscaled chart), AFTER selecting P and K (no claim of the sharper manuscript
pre-L bills). Branch and other flagged terms not asserting representational norms from these.
-/
set_option autoImplicit false
-- tune later
set_option maxHeartbeats 150000
noncomputable section
namespace YM.MatchingLedger.Gazette
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Metric
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio)

section plant
variable {E ι : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {Zb : ℝ} {K : ChartRatio G} (P : E →L[ℝ] Chip (Kernel G ι))

def aim (i : ι) := ContinuousLinearMap.proj (φ:=fun _ : ι=> G.Color) i ∘L ((tint G _).toContinuousLinearMap ∘L P)
lemma aimed (hP : ∀ x : E, ‖P x‖ ≤ ‖x‖)(i : ι) : ‖aim P i‖ ≤ shade G := (aim P i).opNorm_le_bound (shade_pos _).le fun x=> (tint_limit (P x) i).trans (mul_le_mul_of_nonneg_left (hP x) (shade_pos G).le)
lemma paint_lim (hP : ∀ x : E, ‖P x‖ ≤ ‖x‖){x : E} (hx:‖x‖ ≤1) (i : ι) : Allows n (aim P i) x (shade G):= by
  have h: ‖aim P i x‖ ≤ shade G * ‖x‖ := ((aim P i).le_opNorm ..).trans (mul_le_mul_of_nonneg_right (aimed P hP i) (norm_nonneg _))
  exact allows_linear (aimed P hP i) (h.trans (mul_le_of_le_one_right (shade_pos G).le hx))

lemma paint_book (Hp : PaintSupply G n Zb) (hP : ∀ x : E, ‖P x‖ ≤ ‖x‖){x : E} (hx:‖x‖ ≤1) (i : ι) :
    Allows n (fun z=>G.mat (launch (P z) i)) x (outerCost G n Zb):= by
  have h := paint_lim (n:=n) P hP hx i
  exact (Hp.2 _ h.value).comp h

variable {α : Type} [Fintype α] {x : Chip (Kernel G ι ⊕ α)} {y : Chip (α ⊕ Kernel G ι)}
lemma paintL (Hp : PaintSupply G n Zb) (hX : ‖x‖≤1) (i:ι) : Allows n (fun x=>G.mat (launch (binL x) i)) x (outerCost G n Zb) := by
  exact paint_book (G:=G) (ι:=ι) (E:=Chip (Kernel G ι ⊕ α)) (x:=x) binL Hp (fun z : Chip (Kernel G ι ⊕ α)=> binL_le z) hX i
lemma paintR (Hp : PaintSupply G n Zb) (hX : ‖y‖≤1) (i:ι) : Allows n (fun y=>G.mat (launch (binR y) i)) y (outerCost G n Zb) := by
  exact paint_book (G:=G) (ι:=ι) (E:=Chip (α ⊕ Kernel G ι)) (x:=y) binR Hp (fun z : Chip (α ⊕ Kernel G ι)=> binR_le z) hX i
lemma aimLimit (hX : ‖x‖≤1) (i:ι) : Allows n (aim binL i) x (shade G):= paint_lim (G:=G) (E:=Chip (Kernel G ι ⊕ α)) (x:=x) binL (fun z : Chip (Kernel G ι ⊕ α)=> binL_le z) hX i
lemma allow_here (i : ι) {d : G.Color→ℝ} (ht:‖x‖ ≤1) (hv: Allows n d ((aim binL i) x) Zb) :
    Allows n (fun z=> d ((tint G ι (binL z)) i)) x (composeCost n Zb (shade G)) :=
  by
    change Allows n (fun z => d ((aim (E:=Chip (Kernel G ι ⊕ α)) binL i) z)) x _
    exact Allows.comp (E:=Chip (Kernel G ι ⊕ α)) (F:=G.Color) (x:=x) (f:= ⇑(aim (ι:=ι) (E:=Chip (Kernel G ι ⊕ α)) binL i)) (g:=d) hv (aimLimit (x:=x) ht i)
end plant

def jac (A : ChartRatio G) (x : G.Color) := Real.log (A.J x)
def salary (A : ChartRatio G) (z : Site c) (x : Chip (Meter F G)) : ℝ := ∑ i∈located (area F) {z}, jac A ((tint G F.Free (binL x)) i)
def editorial (A : ChartRatio G) (x : Chip (Meter F G)) := ∑ i, jac A ((tint G F.Free (binL x)) i)
lemma edit (A : ChartRatio G) (x : Chip (Meter F G)) : editorial F A x=total Finset.univ (fun z=> salary F A z x) := by
  unfold editorial total salary; rw [total_at,loc_all (_ : F.Free → Site c)]
lemma salary_eq (A : ChartRatio G) {z : Site c} {x y : Chip (Meter F G)} (h : Set.EqOn x y (seats (G:=G) F z)): salary F A z x=salary F A z y:= by
  apply Finset.sum_congr rfl; intro i hi; apply congr_arg; apply tint_eq; intro j
  have hz : atlas (G:=G) F (.inl (i,j))=z := Finset.mem_singleton.mp (show area F i ∈ ({z} : Support c) from loc.mp hi)
  exact h ((loc (a:=atlas F) (i:=.inl (i,j)) (s:=ribbon (S:=S) z)).mpr (by rw [hz]; exact halo_subset _ _ (Finset.mem_singleton_self _)))
lemma salary_port (A : ChartRatio G)(z : Site c) : Books.Restricted (salary F A z) (seats F z):= by
  refine Filter.Eventually.of_forall (fun i=> salary_eq F A ?_)
  intro j hj; rw [Books.crop_apply,if_pos]; exact hj

lemma duet (U : Config G f) (V : Config G c)(t : S.Choices) (z : Site c) : bill S U V t z=
    (∑ i∈located (region (α:=PlaqAxes) S) {z}, G.price (faceValue U i)) + S.kernel.penalty*∑ i:Axis, G.price (V (z,i)*(S.prediction U t (z,i))⁻¹) := by
  unfold bill face thread toll wire; simp_rw [G.chord_price]; rw [← Finset.mul_sum, ← Finset.mul_sum]; ring

lemma film (U : Config G f)(V : Config G c)(t t' : S.Choices) (h : S.prediction U t=S.prediction U t') (z : Site c): bill S U V t z=bill S U V t' z := by unfold bill; rw [h]

-- numerical permits (independent of how exact theory obtained its choice of this A). The kernel uses a different Jacobian Z cost in the density.
structure Budget (G : Gauge) (A : ChartRatio G) (n : ℕ) where
  ink : ℝ
  dye : ℝ
  pale : ℝ
  glow : ℝ
  pay : ℝ
  hr : ℝ
  waist : ℝ
  indexes : ℝ
  nn : 2 ≤ n
  paint : PaintSupply G (n+1) ink
  launch : ExpReceipt G (n+1) dye
  law : LogReceipt G pale glow
  marks : 0<pay
  plate : FocusReceipt G n pay hr
  right : LocalRatio A
  small : 0 < waist
  cap : 0 ≤ indexes
  covers (x : G.Color) (h: ‖x‖ ≤ waist) : Allows n (jac A) x indexes
  fees : waist < A.radius -- later bump
namespace Budget
lemma months (A : ChartRatio G) (L : LocalRatio A) (n : ℕ)(hn : 2≤n) : Nonempty (Budget G A n) := by
  obtain ⟨Z,hZ⟩ := paint_supply G (n+1)
  obtain ⟨C,-,hC⟩:= exp_receipt G (n+1); obtain ⟨e,d,he⟩:= log_receipt G; obtain ⟨K,r,hK,H⟩ := focus_receipt G n
  have hr : 0 < A.radius:= L.patch
  let a:= A.radius/2
  have he' (x : G.Color) (hx:x ∈ closedBall 0 a): ContDiffAt ℝ ω (jac A) x:= by
    apply ContDiffAt.log (L.germ _ (closedBall_subset_ball (half_lt_self hr) hx)); exact (L.pos _ (closedBall_subset_ball (half_lt_self hr) hx)).ne'
  obtain ⟨B,hB,Y⟩:= exists_allows (isCompact_closedBall (0:G.Color) a) he' n
  exact ⟨⟨Z,C,e,d,K,r,a,B,hn,hZ,hC,he,hK,H,L,half_pos hr,hB,fun _ hx=> Y _ (by simpa using hx),half_lt_self hr⟩⟩

variable {A : ChartRatio G} {n : ℕ} (H : Budget G A n)

-- use loose common ink/scale bounds. after block.
def leaf := outerCost G (n+1) H.ink + ‖(1:G.Mat)‖
lemma leaf_pos : 0<H.leaf := (outer_pos G _ H.paint.1).trans_le (le_add_of_nonneg_right (by positivity))
lemma leaf_one : ‖(1:G.Mat)‖≤H.leaf :=le_add_of_nonneg_left (outer_pos G _ H.paint.1).le
lemma leaf_top : outerCost G (n+1) H.ink ≤ H.leaf:= le_add_of_nonneg_right (norm_nonneg _)
lemma lamp : Inputs (litter (G:=G) F) (n+1) H.leaf := by
  refine ⟨litter_zero F,H.leaf_pos.le,?_⟩
  intro e x hx
  by_cases hh:e∈F.trunks
  · simp_rw [show ∀ x,G.mat (litter (G:=G) F x e)=1 from fun x=>congr_arg G.mat (F.on_tree _ ⟨_,hh⟩)]
    apply allows_const; exact H.leaf_one
  have hj (x : Chip (Meter F G)) : litter F x e= Gazette.launch (ι:=F.Free) (binL x) ⟨e,hh⟩:= F.off_tree _ ⟨e,hh⟩
  simp_rw [hj]; exact (paintL (ι:=F.Free) H.paint hx ⟨e, hh⟩).mono (H.leaf_top)
lemma violet : Inputs (venue (G:=G) F) (n+1) H.leaf:= ⟨venue_zero F,H.leaf_pos.le,fun i _ hx=> (paintR (ι:= Bond c) H.paint hx i).mono H.leaf_top⟩

def room (P : Patch) (K : KernelChoices):= predictionRadius P G K n H.dye H.leaf H.pale H.glow H.hr
def space (P : Patch) (K : KernelChoices):= min 1 (min (H.room P K / 2) (H.waist / shade G))
lemma space_small (P K): H.space P K ≤ 1 := min_le_left ..
variable {x : Chip (Meter F G)} (hx:‖x‖ ≤ H.space S.patch S.kernel)
local notation "κ" => S.kernel
local notation "P" => S.patch

include F in
lemma space_pos : 0<H.space P κ:=lt_min one_pos (lt_min (half_pos (prediction_radius_pos S (H.lamp F) H.nn H.launch H.law H.plate)) (div_pos H.small (shade_pos G)))
lemma volume (hp:‖x‖ ≤ H.space P κ) : x∈ball 0 (H.room P κ):= by
  have hm : 0< H.room P κ := prediction_radius_pos S (H.lamp F) H.nn H.launch H.law H.plate
  rw [mem_ball_zero_iff]; exact lt_of_le_of_lt ((hp.trans (min_le_right ..)).trans (min_le_left ..)) (half_lt_self hm)

include hx
lemma ignored (s t : S.Choices) (z : Site c): dues S F G s z x= dues S F G t z x:= film _ _ s t (picked_tags S (H.lamp F) H.nn H.launch H.law x (H.volume F hx) _ _) z
lemma aims (i : F.Free) : ‖(aim binL i) x‖≤H.waist:= by
  have h:‖(aim binL i) x‖ ≤ shade G *‖x‖:= (tint_limit (G:=G) (binL x) i).trans (mul_le_mul_of_nonneg_left (binL_le _) (shade_pos G).le)
  refine h.trans ?_; rw [mul_comm]; exact (le_div_iff₀ (shade_pos G)).1 (hx.trans ((min_le_right ..).trans (min_le_right ..)))

def bondBill (p : Patch) := priceCost G (2^n * H.leaf * composeCost n H.pay (connectorCost p G n H.dye H.leaf))
def pathBill := priceCost G (travelCost G n 4 H.leaf)
def yard (p : Patch) (K : KernelChoices):= faceRent p * H.pathBill + K.penalty*(Fintype.card Axis*H.bondBill p)
lemma calendar (t : S.Choices)(z : Site c) : Allows n (dues S F G t z) x (H.yard P κ):= by
  have he := hx.trans (H.space_small ..)
  let U (x:Chip (Meter F G)):= litter F x; let V (x:Chip (Meter F G)):=venue F x
  let W (i : Cell f) (x : Chip (Meter F G)):= G.price (faceValue (U x) i)
  have hW (i : Cell f) : Allows n (W i) x H.pathBill:=
    (travel_jets (fun i=> ((H.lamp F).2.2 i x he).order (Nat.le_succ n)) (w:=square i.2.val.1 i.2.val.2) i.1 (a:=4) (by simp [square])).price (f:=fun x=> faceValue (U x) i)
  have h : Allows n (fun x=> faceRent P *0 + ∑ i∈located (region (α:=PlaqAxes) S) {z}, W i x) x (faceRent P * H.pathBill) := by
    have he := allows_sum (s:=located (region (α:=PlaqAxes) S) {z}) fun i _=> hW i
    rw [Finset.sum_const,nsmul_eq_mul, region_size,Finset.card_singleton,Nat.mul_one] at he
    simp only [mul_zero, zero_add]; exact he
  simp only [mul_zero,zero_add] at h
  let Y (i : Bond c) (x : Chip (Meter F G)) := G.price (V x i*(S.prediction (U x) t i)⁻¹)
  have hY (i) : Allows n (Y i) x (H.bondBill P) := (((H.violet F).2.2 i x he).order (Nat.le_succ n)|>.times
    ((prediction_pay S (H.lamp F) H.nn H.launch H.law H.plate _ (H.volume F hx) t i).inverse (f:=fun x=> S.prediction (U x) t i))).price (f:=fun x=> V x i*(S.prediction (U x) t i)⁻¹) -- infer times domain
  have hy := (allows_sum (s:=Finset.univ) fun (i:Axis) _=> hY (z,i)).smul (κ).penalty
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,abs_of_nonneg (κ).penalty_pos.le] at hy
  rw [show dues S F G t z=(fun x=> _ + _) from funext (fun x=> duet (litter F x) (venue F x) t z)]
  exact h.add hy

def salaries (p : Patch) := (linkRent p : ℝ)* composeCost n H.indexes (shade G)
lemma salary_pay (z : Site c) : Allows n (salary F A z) x (H.salaries P):= by
  let k:= composeCost n H.indexes (shade G)
  have ht := hx.trans (H.space_small ..)
  have hp (i : F.Free) : Allows n (fun z=>jac A ((tint G F.Free (binL z)) i)) x k :=
    allow_here i ht (H.covers _ (H.aims F hx i))
  have he := allows_sum (s:=located (area F) {z}) fun i _=> hp i
  rw [Finset.sum_const,nsmul_eq_mul] at he
  have hQ : (located (area F) {z}).card ≤ linkRent P:= by simpa only [linkRent,Finset.card_singleton,Nat.mul_one] using free_size S {z} F
  unfold k at he; apply he.mono; apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hQ); unfold composeCost; positivity [H.cap,shade_pos G]

-- Note yard needn't be used as-is. Make a positive budget without e.g. presence of any free links.
def income (p : Patch) (K : KernelChoices) := 1 + |H.yard p K| + |H.salaries p|
omit hx in
lemma income_one (p : Patch) (K : KernelChoices):1≤H.income p K:= le_trans (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_right (abs_nonneg _))
lemma duty (t : S.Choices)(z : Site c): Allows n (dues S F G t z) x (H.income P κ):= (H.calendar F hx t z).mono ((le_abs_self _).trans (le_trans (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_right (abs_nonneg _))))
lemma issued (z : Site c): Allows n (salary F A z) x (H.income P κ):= (H.salary_pay F hx z).mono ((le_abs_self _).trans (le_add_of_nonneg_left (by positivity)))
end Budget

end YM.MatchingLedger.Gazette
