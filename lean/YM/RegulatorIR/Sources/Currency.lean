import YM.RegulatorIR.Sources.Faith

/-!
# Root-test grant from canonical kme atom presentations

Derivative addresses at actual w∈physical profile support. Tag = (operator
component derivatives, continuous address). Weight bills k story paid once.
Real-polynomial maps. No fabricated output estimates accepted. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Labels Source Aperture Address.Calendar
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
-- tagged coordinates. simpler code fixed padded tuple. repeated-order testing. top spans poly. include $tsupport$. avoid all tests in exhibited kernels except compact ones; manuscript addresses may be signed so not assuming single product profile representation.
abbrev Category (v:ℕ) := Fin (v+1) × (Fin v→ Axis)
abbrev Token (v:ℕ):= Category v×Room
variable (J: Category m)
def pointsR (i : Fin J.1.val): Room:= Pi.single (J.2 ⟨i.val,lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ J.1.isLt)⟩) 1
def feeD (φ:Room→ℝ)(p : Category m)(x:Room):=iteratedFDeriv ℝ p.fst.val φ x (pointsR p)
def fee_at (φ:Room→ℝ)(l:ℝ)(p:Category m)(x:Room):= l^p.fst.val*feeD φ p x
lemma wind_visible (J : Category m) {φ: Room→ℝ}(h:ContDiff ℝ m φ)(l:ℝ): Continuous (fee_at φ l J):= by
 apply continuous_const.mul; exact (ContinuousMultilinearMap.apply ℝ (fun _:Fin _=>Room) ℝ (pointsR J)).continuous.comp (h.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ J.1.isLt))
lemma fee_birth {φ:Room→ℝ}(l:ℝ)(p:Category m)(x:Room): fee_at φ l p x≠0 → x∈tsupport φ:= by
 intro h; apply support_iteratedFDeriv_subset (𝕜:=ℝ) p.1.val;intro hc;apply h;simp [feeD,fee_at,hc]
-- exist measurable_space product through pi finite? Fin top.

def codeS (l:ℝ)(x:Room)(φ:Room→ℝ) (h:ContDiff ℝ m φ): Address.Calendar.Script (Token m) where
 test k y:= fee_at φ l k.1 (y-x)
 regular := by
    let P:=Category m; let v(i:P)(p: Token m×Room):= if p.1.1=i then fee_at φ l i (p.2-x) else 0
    rw [show uncurry _=∑ i:P,v i from ?_]; swap
    · ext1 t; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem t.fst.fst (mem_univ _)]; exact (if_pos rfl).symm; intro j hj he; exact if_neg (Ne.symm he)
    rw [show (∑ i:P,v i)=fun a=> (∑ i:P,v i a) from funext (fun i=>Finset.sum_apply ..)]; apply Finset.measurable_sum
    intro i hi
    refine Measurable.ite ?_ ((wind_visible i h l).measurable.comp (measurable_snd.sub_const x)) measurable_const
    exact (measurableSet_singleton i).preimage (measurable_fst.comp measurable_fst)

lemma evaluates (l:ℝ)(p:Cover)(φ:Room→ℝ)(h:ContDiff ℝ m φ)(x:Room)(y:Token m)(v:Room) : (codeS l x φ h).test y (slide l p+l • v)=feeD (perch φ l x p) y.1 v:=by
 unfold feeD; rw [beamAt h (by have ht:= y.1.1.isLt;omega),show slide l p-x+l • v=slide l p+l • v-x by abel]; rfl
lemma parish {l:ℝ} (φ: PhaseTests d) {c:ℝ≥0∞} (x:Room) (Z:Set Room) (U: tsupport φ.phi⊆Z) (V: Z ⊆ Metric.closedBall 0 φ.radius)
    (hp:ContDiff ℝ m φ.phi)(hl:0<l)(hh:l≤1)(h:∀ p:Category m,∀ v:Room, ‖feeD φ.phi p v‖ₑ≤c): Bills (codeS l x φ.phi hp) {w | w-x ∈ Z} x φ.radius c:=by
 refine ⟨fun v hv=>?_,?_⟩
 · have he:=V hv; change dist (v-x) (0:Room)≤ _ at he; simpa [dist_eq_norm] using he
 intro z v hv; refine ⟨U (fee_birth l z.1 _ hv),?_⟩
 change ‖l^_*_‖ₑ≤ _; rw [enorm_mul]; apply (mul_le_mul' (show ‖l^z.1.1.val‖ₑ ≤ 1 from ?_) (h z.1 (v-x))).trans; rw [one_mul]
 rw [← ofReal_norm, Real.norm_of_nonneg (pow_nonneg hl.le _),← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hl.le hh)

variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
variable {F:Labels.Frame G d}{Hol:Hol G}(Z: Fabric R F Hol)
-- invoke from `T^h=...` and `Y`. Lantern assumes not compact? use all bounded-root derivatives compact. no `sensors` invented whose value includes engineering factors.

def LanternTag (K: TagList (Foot G) (Token m) j)(v:Tuple (Foot G) j)(φ:Room→ℝ)(u:Token m):= K.value v u * feeD φ u.1 (K.placement u)
structure Bondage (K: TagList (Foot G) (Token m) j)(l:Page M)(r:ℕ) : Prop where
 shines : ∀ f: Room→ℝ, HasCompactSupport f→ ContDiff ℝ m f → ∀ v :Tuple _ j, pyramid R T Z l f r j v=∫ u, LanternTag K v f u ∂(K.rolls v)

def meterC (w:Page M):Address.Calendar (S.l w) (Foot G):= latticeWalk G.ColorIndex (S.l w)
variable (Φ: W → PhaseTests d)

lemma firmness (s:ℝ) (hs:0<s)(φ:Room→ℝ)(h:IsCompact (tsupport φ))(x:Room)(v:Cover):HasCompactSupport (perch φ s x v):=by
 let y:= slide s v-x
 let f (w:Room):= y+s • w
 let g (w:Room):= s⁻¹ • (w-y);
 have hg:Continuous g:= by unfold g; fun_prop
 apply IsCompact.of_isClosed_subset (h.image hg) isClosed_closure; refine closure_minimal ?_ (h.image hg).isClosed
 intro z hz;refine ⟨f z,subset_closure hz,?_⟩; simp [g,f, smul_smul,hs.ne']

lemma support_eval (φ:PhaseTests d): IsCompact (tsupport φ.phi):= IsCompact.of_isClosed_subset (isCompact_closedBall 0 φ.radius) isClosed_closure φ.uses

variable (K:TagList (Foot G) (Token m) j)(l:Page M)(ho:Bondage R T Z K l e)(x:Room)
include ho
lemma repair {h:ContDiff ℝ m (Φ l.bindW).phi}(t:Tuple (Foot G) j)(z:Cover):
 sparks R T Z Φ l x z e j t=softL (S.l l) d * Address.Calendar.spoke (meterC (S:=S) l) K (codeS (S.l l) x (Φ l.bindW).phi h) z t:=by
 let f:= (Φ l.bindW).phi; let v:=perch f (S.l l) x z; let Q:= meterC (S:=S) l (G:=G); let s:= (Q.sends z).symm t
 change softL _ _*pyramid R T Z l v e j s=_
 have hx: ContDiff ℝ m v:=by apply h.comp (f:=fun a:Room=>slide (S.l l) z-x+S.l l • a); fun_prop
 rw [ho.shines v (firmness (S.l l) (S.hl _) _ (support_eval ..) x z) hx]; unfold spoke;apply congr_arg;apply integral_congr_ae (μ:=K.rolls s); filter_upwards with y; unfold LanternTag weighed; rw [evaluates]

variable (P: Passage R)(hc: Common R)(hv:R.Follows T) (G₀: Milieu S T k p L)
include P hc hv G₀
lemma localRestore {h: ContDiff ℝ m (Φ l.bindW).phi}(he:e ≤ p):
 (fresco R T Z Φ).main (leafX l x) e j= material (meterC (S:=S) l) K (codeS (S.l l) x (Φ l.bindW).phi h) d:=by
 ext1 t;rw [finance R T Z Φ P hc hv x G₀ l he]; rw [material,Pi.smul_apply,calyx,smul_eq_mul,← tsum_mul_left];exact tsum_congr fun i=> repair R T Z Φ K l ho x _ _
end YM.RegulatorIR.Sources
