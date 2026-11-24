import YM.Integration.WilsonInvariantActionRegisteredHearing
import YM.Integration.WilsonMatrixTicketLanesRegisteredValue

/-! Charge the two earlier terms and the entire signed third cumulant in the
actual conditional Wilson tower by the true absolute first moment of the
changed vacuum. This uses only the submitted operators' two gross prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumIncome
open Function Filter Set MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
open private five from YM.Integration.WilsonInvariantActionPriorHearing
open private fine from YM.Integration.WilsonMatrixTicketLanesRegisteredValue
open scoped Classical BigOperators Topology
variable {X:Type*} [MeasurableSpace X]

private structure State (E:readings X →ₗ[ℝ] ℝ):Prop where
  one:E 1=1
  pos:∀a:readings X,(∀x,0≤a.val x) → 0≤E a

def absolute (w:readings X):readings X:=
  ⟨fun x=>|w.val x|,w.property.meas.abs,w.property.cost.choose,fun x=>by simpa using w.property.cost.choose_spec x⟩

private theorem mono {E:readings X →ₗ[ℝ] ℝ} (s:State E) {a b:readings X} (h:∀x,a.val x≤b.val x):E a≤E b:=by
  have p:=s.pos (b-a) fun x=>sub_nonneg.mpr (h x)
  rwa [map_sub,sub_nonneg] at p

private theorem amount {E:readings X →ₗ[ℝ] ℝ} (s:State E) (a b:readings X) (h:∀x,|a.val x|≤b.val x):|E a|≤E b:=by
  have lower:=mono s (a:=-a) (b:=b) fun x=>(neg_le_abs _).trans (h x)
  rw [map_neg] at lower
  exact abs_le.mpr ⟨by linarith only [lower],mono s fun x=>(le_abs_self _).trans (h x)⟩

private theorem cap {E:readings X →ₗ[ℝ] ℝ} (s:State E) (a:readings X) {K:ℝ} (h:∀x,|a.val x|≤K):|E a|≤K:=by
  have upper:=amount s a (K • 1) fun x=>by change |a.val x|≤K*1;simpa only [mul_one] using h x
  simpa only [map_smul,smul_eq_mul,s.one,mul_one] using upper

private theorem weighted {E:readings X →ₗ[ℝ] ℝ} (s:State E) (a w:readings X) {K:ℝ}
    (h:∀x,|a.val x|≤K):|E (a*w)|≤K*E (absolute w):=by
  have upper:=amount s (a*w) (K • absolute w) fun x=>by
    change |a.val x*w.val x|≤K*|w.val x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h x) (abs_nonneg _)
  simpa only [map_smul,smul_eq_mul] using upper

private theorem six {a b c d e f K:ℝ} (ha:|a|≤K) (hb:|b|≤K) (hc:|c|≤K) (hd:|d|≤K)
    (he:|e|≤K) (hf:|f|≤K):|a-b-c-d+e+f|≤6*K:=by
  rw [abs_le] at ha hb hc hd he hf ⊢
  constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2,he.1,he.2,hf.1,hf.2]

private theorem third {E:readings X →ₗ[ℝ] ℝ} (s:State E) (a b w:readings X) {A B:ℝ} (an:0≤A) (bn:0≤B)
    (fa:∀x,|a.val x|≤A) (fb:∀x,|b.val x|≤B):
    |cubic E a b w|≤6*(A*B)*E (absolute w):=by
  let W:=E (absolute w)
  have mw:|E w|≤W:=amount s w (absolute w) fun _=>le_rfl
  have ab (x:X):|(a*b).val x|≤A*B:=by
    change |a.val x*b.val x|≤A*B
    rw [abs_mul];exact mul_le_mul (fa x) (fb x) (abs_nonneg _) an
  have ma:=cap s a fa
  have mb:=cap s b fb
  have pair:=cap s (a*b) ab
  have aw:=weighted s a w fa
  have bw:=weighted s b w fb
  have total:=weighted s (a*b) w ab
  have scalar:|E a*E b*E w|≤A*B*W:=by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul ma mb (abs_nonneg _) an) mw (abs_nonneg _) (mul_nonneg an bn)
  rw [mul_assoc (6:ℝ)]
  apply six total _ _ _ scalar scalar
  · rw [abs_mul];exact mul_le_mul pair mw (abs_nonneg _) (mul_nonneg an bn)
  · rw [abs_mul]
    calc _≤(A*W)*B:=mul_le_mul aw mb (abs_nonneg _) (mul_nonneg an (s.pos _ fun x=>abs_nonneg _))
         _=A*B*W:=by ring
  · rw [abs_mul]
    calc _≤(B*W)*A:=mul_le_mul bw ma (abs_nonneg _) (mul_nonneg bn (s.pos _ fun x=>abs_nonneg _))
         _=A*B*W:=by ring

private theorem second {E:readings X →ₗ[ℝ] ℝ} (s:State E) (a w:readings X) {A:ℝ} (an:0≤A) (fa:∀x,|a.val x|≤A):
    |covariance E w a|≤2*A*E (absolute w):=by
  let K:=A*E (absolute w)
  have first:|E (w*a)|≤K:=by rw [mul_comm w];exact weighted s a w fa
  have last:|E w*E a|≤K:=by
    rw [mul_comm (E w),abs_mul]
    exact mul_le_mul (cap s a fa) (amount s w (absolute w) fun _=>le_rfl) (abs_nonneg _) an
  exact (abs_sub _ _).trans (by change _≤2*A*E (absolute w);dsimp only [K] at first last;linarith only [first,last])

private theorem rotate {X Y:Type*} [CommRing X] [CommRing Y] (E:X → Y) (a b w:X):
    cubic E w a b=cubic E a b w:=by
  have product:w*a*b=a*b*w:=by ring
  rw [cubic,cubic,product,mul_comm w a,mul_comm w b]
  ring

variable {G:Gauge} (R:Run G) {N k per:ℕ}
local notation "lower" => Config G (R.family.side k per)
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "Ω" => (lower × upper)
local notation "κ" => ActualWilsonConditionalRoots.fibre R.family (N:=N)
local notation "μ" => scene R.family.path N per k

private def eval {X:Type*} [MeasurableSpace X] (x:X):readings X →ₗ[ℝ]ℝ where
  toFun f:=f.val x
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private theorem base (live:k<N):State (earlier R (p:=per) live):=by
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live.le
  constructor
  · change ∫_:lower,(1:ℝ) ∂μ=1
    simp
  · intro a nonnegative
    exact integral_nonneg nonnegative

private theorem fibreState (live:k<N) (V:lower):State ((eval V).comp (conditional R (p:=per) live)):=by
  letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
  constructor
  · change ∫_:upper,(1:ℝ) ∂κ V=1
    simp
  · intro a nonnegative
    exact integral_nonneg (fun U=>nonnegative (V,U))

private theorem jointState (live:k<N):State (joint R (p:=per) live):=by
  let E:=earlier R (p:=per) live
  let I:=conditional R (p:=per) live
  constructor
  · change E (I 1)=1
    have one:I 1=1:=by
      apply Subtype.ext;funext V
      exact (fibreState R live V).one
    rw [one];exact (base R live).one
  · intro a nonnegative
    exact (base R live).pos (I a) fun V=>(fibreState R live V).pos a nonnegative

/-- The two previously retained incomes and the signed sum of all five,
each on its original probability, at the actual registered parent sites. -/
theorem original (live:k<N) (a b w:readings Ω) {A B:ℝ} (an:0≤A) (bn:0≤B)
    (fa:∀x,|a.val x|≤A) (fb:∀x,|b.val x|≤B):
    let E:=earlier R (p:=per) live
    let I:=conditional R (p:=per) live
    let L:=joint R live (absolute w)
    |covariance E (I w) (covariance I a b)|≤4*(A*B)*L ∧
      |cubic E (I w) (I a) (I b)|≤6*(A*B)*L ∧
      |receipts R live a b w|≤6*(A*B)*L:=by
  let E:=earlier R (p:=per) live
  let I:=conditional R (p:=per) live
  let L:=joint R live (absolute w)
  have aa(V:lower):|(I a).val V|≤A:=cap (fibreState R live V) a fa
  have bb(V:lower):|(I b).val V|≤B:=cap (fibreState R live V) b fb
  have cover (V:lower):|(covariance I a b).val V|≤2*(A*B):=by
    have hab(x:Ω):|(a*b).val x|≤A*B:=by
      change |a.val x*b.val x|≤A*B
      rw [abs_mul];exact mul_le_mul (fa x) (fb x) (abs_nonneg _) an
    have one:=cap (fibreState R live V) (a*b) hab
    have two:|(I a).val V*(I b).val V|≤A*B:=by rw [abs_mul];exact mul_le_mul (aa V) (bb V) (abs_nonneg _) an
    apply (abs_sub _ _).trans
    change |(I (a*b)).val V|+|(I a).val V*(I b).val V|≤2*(A*B)
    change |(I (a*b)).val V|≤A*B at one
    linarith only [one,two]
  have contract:E (absolute (I w))≤L:=
    mono (base R live) fun V=>amount (fibreState R live V) w (absolute w) fun _=>le_rfl
  dsimp only []
  refine ⟨?_,?_,?_⟩
  · have pre:=second (base R live) (covariance I a b) (I w) (by positivity) cover
    exact pre.trans (by
      calc
        _≤2*(2*(A*B))*L:=mul_le_mul_of_nonneg_left contract (by positivity)
        _=4*(A*B)*L:=by ring)
  · have acc:=third (base R live) (I a) (I b) (I w) an bn aa bb
    rw [rotate E (I a) (I b) (I w)]
    exact acc.trans (mul_le_mul_of_nonneg_left contract (by positivity))
  · unfold receipts
    rw [←five]
    exact third (jointState R live) a b w an bn fa fb

/-- A genuine reported fine-field score has its true Wilson, rather than
an arbitrarily chosen older-state, absolute first moment. -/
theorem fineMass (inside:k+1≤N) (w:readings Ω) (v:upper → ℝ) (source:∀V U,w.val (V,U)=v U):
    joint R (inside: k+1≤N) (absolute w)=∫U,|v U| ∂scene R.family.path N per (k+1):=by
  exact fine R inside (absolute w) (fun V U=>congrArg abs ((source V U).trans (source 1 U).symm)) |>.trans
    (integral_congr_ae (ae_of_all _ (fun U=>congrArg abs (source 1 U))))

end YM.Integration.WilsonMatrixTicketLanesVacuumIncome
