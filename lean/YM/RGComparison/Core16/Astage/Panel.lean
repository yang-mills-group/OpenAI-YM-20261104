import YM.RGComparison.Core16.Astage.Window

/-!
# Precision upgrade -- bootstrap via pairs

Packed pairs with a FIXED TWO slots (the same real EUCLIDEAN fields, full expectation).
Use for *separated* q:Grams, genuine smoothing allowed. Keep separation
receipt. Prices here are at SUBPOWER on the spatial scale; obtain from actual period/placement
uniformity of Services. Always use one Final.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Panel
open Filter Function Real Metric Set MeasureTheory OPE
open Table Orbits Word
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
    (T:Spec.Final C F S) (d:ℕ) {ι:Type} {l:Filter ι}
    {V W:Type*}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V]
    [NormedAddCommGroup W][NormedSpace ℂ W]

-- Use point bounds from the same hierarchy -> costs as operator norm on fixed frames. Used only
-- finitely many times, so not silently pricing native cell marker copies here.
lemma lift_price (v:ι→ V→L[ℂ] W){u:ι→ℝ}{c:ℝ} (h:Tendsto u l atTop)(hh:∀ x:V,
    RateLE l u (fun i=> v i x) c): RateLE l u v c:=by
    let X:= Module.finBasis ℂ V
    let A(j):=LinearMap.toContinuousLinearMap (X.coord j); let J:=Fin (Module.finrank ℂ V)
    let f(j:J)(i:ι):= ‖A j‖ * ‖v i (X j)‖
    have hz:RateLE l u (fun i=> ∑ j:J,f j i) c:=by
       apply RateLE.sum h; intro j _; simpa only [zero_add] using (RateLE.const ‖A j‖ h).mul (hh (X j)|>.norm)
    apply hz.of_norm_le; refine Eventually.of_forall fun i=> (v i).opNorm_le_bound (Finset.sum_nonneg (fun j _=> mul_nonneg (norm_nonneg _) (norm_nonneg _))) ?_; intro x
    have he : v i x=∑ j:J,A j x • v i (X j):= by
       nth_rw 1 [← X.sum_repr x]; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => map_smul ..
    rw [he]; apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j _=>?_ ; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right ((A j).le_opNorm _) (norm_nonneg _)).trans_eq (mul_right_comm ..)

-- typeclass unfolding of repeated Field in CLM targets needs shortcut
scoped instance (priority := high) sem {k:Register G}(T:Table k)(d:ℕ): SeminormedAddCommGroup (T.Field d):= inferInstanceAs (SeminormedAddCommGroup (k.Ref d ⧸ T.null d))
scoped instance (priority := high) normed {k:Register G}(T:Table k)(d:ℕ):NormedAddCommGroup (T.Field d):= inferInstanceAs (NormedAddCommGroup (k.Ref d ⧸ T.null d))
scoped instance (priority := high) normsp {k:Register G}(T:Table k)(d:ℕ):NormedSpace ℂ (T.Field d):= inferInstanceAs (NormedSpace ℂ (k.Ref d ⧸ T.null d))
local notation "field"=> S.Field d

def body (T:Table C.book)(x:Points 2): field→L[ℂ] field→L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ (Levy.linear₂ (S.classMoment T (fun _=>d) x)))
lemma exposes (T:Table C.book)(x:Points 2)(u v:S.Field d): body d T x u v=Levy.pair d T x u v := rfl

variable (H:Services C F S) {j:ι→ℕ}(t:ℕ) (Z:ι→Points 2) (u:ι→ ℝ)(r:ι→ Viewers T)
    (ht:Tendsto u l atTop) (hK: Kept l u 1 (fun i=>(Z i).ofLp)) [l.NeBot]
set_option quotPrecheck false
include T H hK ht
lemma reads (x x':field) : RateLE l u (fun i=> body d (spectator T (r i)) (Z i) x x') (d+d:ℝ) :=by
    let V':=Fin 2; let d' : V'→ℕ := fun _=>d; let q:Labels S d':=![x,x']; let f:=names q; let w i:= observe (spectator T (r i)) ((Z i).ofLp) f
    let t:Empty→ C.book.Token:=Empty.elim; let Y:ι→ Empty→ E4:=fun _=>Empty.elim
    have hh:Kept l u 1 Y:= fun _ _=>Eventually.of_forall (fun i z=>Empty.elim z)
    have hs:=viewer_cost (Y:=Y) T H.schedule f t ht r hK hh (fun _ _=>Eventually.of_forall (fun i _ z=>Empty.elim z)) zero_le_one le_rfl
    rw [show sigma f=d+d by simp [sigma,f,names,q,d',V',two_mul], Nat.cast_add, mul_one, show sigma t=0 by simp [sigma], Nat.cast_zero, zero_mul, add_zero] at hs
    apply hs.congr
    filter_upwards [hK.inject] with i hi
    let e:= Equiv.sumEmpty V' Empty; let M:= spectator T (r i); let k:Fin 2→E4:=(Z i).ofLp; let HSym: M.Symmetric:= (spectate T (r i)).laws.toSymmetric
    change observe M _ _ = _; rw [show beside ((Z i).ofLp) (Y i) = k ∘ e from (funext fun i=> by cases i; rfl; rename_i z; cases z),show beside f t=f ∘ e from (funext fun i=> by cases i; rfl; rename_i z; cases z), perm_observe M HSym e f hi]; exact (named_fin M HSym f (show Z i ∈ conf 2 from hi))
lemma joint : RateLE l u (fun i=> body (S:=S) d (spectator T (r i)) (Z i)) (d+d:ℝ):=
    lift_price _ ht (fun x=>lift_price _ ht (fun y=>reads T d H Z u r ht hK x y))

omit hK
-- Specializations allow smear profiles on pairs. Z i t may only range over the chosen admissible
-- shapes; integrate with Lebesgue restricted to fixed compact or submanifold profile, etc.
-- Don't assert every such smear is an admitted MAIN REPORT geometry; here only need this smaller
-- receipt on each diagnostic's AUXILIARY geometry (see below).
omit H ht [l.NeBot] in
def Billed {K:Type}[MeasurableSpace K] (r:Viewers T)(μ:Measure K)(w:K→ℂ)(V:K→Points 2):=
    ∀ (x y:field), Integrable (fun j=> w j * body d (spectator T r) (V j) x y) μ

omit H ht [l.NeBot] in
def receipt {K:Type}[MeasurableSpace K](r:Viewers T)(μ:Measure K)(w:K→ℂ)(V:K→Points 2)
    (h:Billed T d r μ w V): field→L[ℂ]field→L[ℂ]ℂ :=
    let f(x y:field):=∫ j,w j * body d (spectator T r) (V j) x y∂μ
    let b:= LinearMap.mk₂ ℂ f
       (fun x y z=>by
          dsimp only [f]; simp_rw [map_add,_root_.add_apply,mul_add]; rw [integral_add (h ..) (h ..)])
       (fun c x y=>by dsimp only [f]; simp_rw [map_smul,_root_.smul_apply,smul_eq_mul,mul_left_comm _ c, integral_const_mul])
       (fun x y z=>by dsimp only [f]; simp_rw [map_add,mul_add]; rw [integral_add (h ..) (h ..)])
       (fun c x y=>by dsimp only [f]; simp_rw [map_smul,smul_eq_mul,mul_left_comm _ c, integral_const_mul])
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b)
omit H ht [l.NeBot] in
lemma receipt_at {K:Type}[MeasurableSpace K](r:Viewers T)(μ:Measure K)(w:K→ℂ)(V:K→Points 2)
    (h:Billed T d r μ w V) (x x':field): receipt T d r μ w V h x x' = ∫ i, w i * Levy.pair d (spectator T r) (V i) x x'∂μ := rfl

lemma budget {K:Type}[Nonempty K][MeasurableSpace K] (μ:ι→Measure K)(w:ι→K→ℂ)(V:ι→K→Points 2)
    (hZ:∀ f:ι→ K, Kept l u 1 (fun i=>(V i (f i)).ofLp)) (hs:RateLE l u (fun i=> ∫ a, ‖w i a‖ ∂μ i) 0) (hw:∀ᶠ i in l, Integrable (w i) (μ i))(he:∀ i, Billed T d (r i) (μ i) (w i) (V i)):
    RateLE l u (fun i=>receipt T d (r i) (μ i) (w i) (V i) (he i)) (d+d:ℝ):=by
    apply lift_price _ ht; intro y; apply lift_price _ ht; intro z x hx
    obtain ⟨a,ha,hb⟩:=exists_between hx
    filter_upwards [hw, hs (x-a) (sub_pos.mpr hb), universalize (V:=K) (p:=fun i j=> ‖body (S:=S) d (spectator T (r i)) (V i j) y z‖≤ exp (a*u i)) (fun g=> reads T d H (fun i=> V i (g i)) u r ht (hZ g) y z a ha)] with i hw hs hV
    let f(j):= w i j * body (S:=S) d (spectator T (r i)) (V i j) y z
    change ‖∫ j, f j ∂μ i‖ ≤ _
    calc _ ≤ ∫ j, ‖w i j‖ * exp (a*u i) ∂μ i:= norm_integral_le_of_norm_le (hw.norm.mul_const _) (Eventually.of_forall (fun j=>by unfold f; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hV _) (norm_nonneg _)))
         _ ≤ exp ((x-a)*u i) * exp (a*u i):= by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans hs) (exp_nonneg _)
         _ = _:= by rw [← Real.exp_add]; ring_nf

-- ONE representative geometry admissible also at exact Gram delay (specialize offsets). applies
-- more generally when X scales subpower in the spatial scale. Keep this explicit weighting.
omit T H ht u [l.NeBot] in
lemma reporting {m:ι→ℕ}(ht:Tendsto m l atTop){a:ℝ}(ha:0<a) (V:ι→Points 2)(hV:∀ᶠ i in l, ∀ j k : Fin 2, j ≠ k → a*C.S.a (m i) ≤ ‖(V i).ofLp j-(V i).ofLp k‖) : Kept l (ruler C m) 1 fun i=> (V i).ofLp:=by
    have hQ:= (Height.mesh (S:=C.S) (show Height C.S l (ruler C m) m 1 from
                 ⟨ht,tendsto_const_nhds.congr' (by filter_upwards [(large_s C ht).eventually_gt_atTop 0] with i hi; rw [show C.S.scale (m i)=ruler C m i from rfl,div_self hi.ne'])⟩))
    intro b hb; have he:= ((RateIs.const (large_s C ht) ha).mul hQ).overtakes (RateLE.exp (-b) (large_s C ht)) (large_s C ht) (by linarith)
    filter_upwards [hV,he] with i hi he j k hk
    exact lt_of_lt_of_le he (hi j k hk)
end YM.RGComparison.Core16.Astage.Panel
