 import YM.Next.FOUNDATIONS.Regular
import YM.RG3.Axial.Revalue
import YM.Next.RANK.Ray
import YM.Push.LOOP_COEFFICIENT.Tangent

/-!
# Small ordinary jets → real local price. II: on the actual gauge patch

Combines the criterion on small (true) log charts with the rectified axial
path comparisons `Spindle.closer` for based links by group exchanges. Only
those *inside* the registered common hull are assumed representable in a
small chart! The extension by zero outside is after a gauge transform held
fixed for all the iterations of LEFT (no map on the measure or changing the
Boltzmann factors is done by this estimate). This version takes even nonzero
mismatch on ordinary jets and needs only raw prices, pays the recenter and
the derivatives at all actual anchors. `Trace.Physical.LogAccuracy` covers
a related criterion on complex cylinders with exact zero mismatch & global
left price; this uses fixed gauges similarly, with the patch on both read
endpoints, and `stationed` instead of differentiating along lines.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Axial
open Function Lattice Wilson RG SelectedOrderedKernels Next.Rank.Spindle MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Config G n → E} {b r k : ℕ} {o : Site n}
  {p : BudgetPoint} {X : Support n} {ε c : ℝ}

/-- Actual link chart at a given physical point, in the based gauge on
just these links. Depends on U but travels as a constant when computing its
jet. -/
def doorway (o : Site n) (b : ℕ) (U : Config G n) : Directions G n :=
  fun e => if h:e∈Room o b then wired 1 o b U ⟨e,h⟩ else 0

-- T ≥ 2*(4*b*threshold) and pays every direction tested INSIDE support.
-- B.power ≥ 2. No volume. Buy support exponent separately.
def dues (p : BudgetPoint) (b : ℕ) := 8*p.threshold * (1+2*(b:ℝ))^p.power
lemma dues_nn (p : BudgetPoint) (b : ℕ) : 0 ≤ dues p b := by
  have h:=p.threshold_pos; unfold dues; positivity
lemma dues_log (p : BudgetPoint) (b : ℕ) : 2*(4*(b:ℝ)*p.threshold) ≤ dues p b := by
  have hx : (1:ℝ) ≤ 1+2*b:=by simp
  have hs := p.power_ge
  have he : (b:ℝ) ≤ (1+(2:ℝ)*b)^p.power:= (show (b:ℝ) ≤ 1+2*b by
    have := Nat.cast_nonneg (α:=ℝ) b; linarith).trans (le_self_pow₀ hx (by omega))
  unfold dues
  rw [mul_assoc (8:ℝ)]
  linarith only [mul_le_mul_of_nonneg_left he p.threshold_pos.le]

lemma arrival (V : Rules G) (hn : 2*(b+1)<n.val) (hp : 4*b*p.threshold ≤ V.c)
    (o : Site n) (U : Config G n) (hu : Healthy p.threshold (Next.Rank.Spindle.patch b o) U) :
    Agrees ↑(Next.Rank.Spindle.patch b o) (gauge (fingers U o) U) (increment 1 (doorway o b U)) ∧
    ‖doorway o b U‖ ≤ dues p b := by
  obtain ⟨hs,he,-⟩:= closer V hn U (o:=o) hu 1 zero_lt_one p.threshold_pos hp
  constructor
  · intro i hi hi'; change spine U o i = G.lieExp (doorway o b U i)*1
    let e : Dim o b := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hi'⟩⟩
    rw [doorway,dif_pos (show i∈Room o b from e.property), mul_one]
    simpa only [e,one_smul] using (he e).symm
  apply (pi_norm_le_iff_of_nonneg (dues_nn ..)).mpr
  intro i; unfold doorway; split
  next hi => exact (norm_le_pi_norm (wired 1 o b U) (⟨i,hi⟩ : Dim o b)).trans (hs.trans (by simpa using dues_log p b))
  simpa using dues_nn p b

def chief (z : Site n → G.El) (X : Support n) (A : Directions G n) : Directions G n :=
  fun i => if i.1∈X ∧ i.1+step i.2∈X then G.adjoint (z i.1) (A i) else 0

@[fun_prop] lemma chief_cd (z : Site n→ G.El) (X : Support n) : ContDiff ℝ ω (chief z X) := by
  apply contDiff_pi.mpr; intro i; unfold chief; split
  · exact (G.adjoint (z i.1)).toContinuousLinearMap.contDiff.comp (contDiff_apply _ G.Color i)
  exact contDiff_const

@[simp] lemma chief_zero (z : Site n→G.El) (X : Support n) : chief z X 0=0 := by funext i; unfold chief; split <;> simp

lemma chief_in (z : Site n→ G.El) (hx : X ⊆ Next.Rank.Spindle.patch b o) (x : Site n) (h : x∈Next.Rank.Spindle.patch b o)
    (A : Directions G n) (ha : p.dirBound x A) : ‖chief z X A‖ ≤ dues p b := by
  apply (pi_norm_le_iff_of_nonneg (dues_nn ..)).mpr
  intro i; unfold chief; split
  next hi =>
    have hp : separation i.1 x ≤ 2*b := le_trans (separation_triangle i.1 o x) (show _ ≤ 2*b by
      have hv := (doors x).mp h; have ha' := (doors _).mp (hx hi.1)
      rw [separation_comm] at ha'; omega)
    have hj : (separation i.1 x:ℝ) ≤ 2*(b:ℝ):=by exact_mod_cast hp
    rw [G.norm_adjoint]; refine (ha i).trans ?_
    refine mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (add_le_add_right hj _) _) (by positivity) (mul_nonneg (by norm_num) p.threshold_pos.le)
    exact le_mul_of_one_le_left p.threshold_pos.le (by norm_num)
  rw [norm_zero]; exact dues_nn ..

variable (hs : GaugeInvariant F) (hl : LocalOn ↑X F)
include hs hl
 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma chief_enters (z : Site n→ G.El) {U W : Config G n} (h : Agrees ↑X (gauge z U) W) (A : Directions G n):
    F (increment U A) = F (increment W (chief z X A)) := by
  rw [← hs z (increment U A)]; apply hl
  intro i hi hj; change _ = G.lieExp _ * W i; rw [← h i hi hj,chief,if_pos ⟨show i.1 ∈ X from hi,show i.1+step i.2∈X from hj⟩,Push.Loops.exp_adjoint]; unfold Lattice.gauge; unfold increment; group

/-- Combined gauge/local pull, still exact without germ hypotheses, also
for iterated LEFT derivatives. No mask carried through this operation; the
jets are of the unmasked representatives in the actual construction. -/
theorem paid (z : Site n→ G.El) {U W : Config G n} (h : Agrees ↑X (gauge z U) W) (l : List (Directions G n)) :
    leftDerivs F l U = leftDerivs F (l.map (chief z X)) W := by
  induction l generalizing U W with
  | nil => exact (hs z U).symm.trans (hl _ _ h)
  | cons i l ih =>
    simp only [leftDerivs,List.map_cons]; apply congr_arg (fun f : ℝ → E => deriv f 0); funext t
    apply ih
    intro e h1 h2; unfold increment chief; rw [← h e h1 h2,Pi.smul_apply,if_pos ⟨show e.1 ∈ X from h1,show e.1+step e.2∈X from h2⟩, ← map_smul,Push.Loops.exp_adjoint]
    unfold Lattice.gauge; simp only [Pi.smul_apply]; group


local notation "hull" => Next.Rank.Spindle.patch

variable (hF : Ordinary (F ∘ increment 1) r k (dues p b) ε c)
  (hX : X ⊆ hull b o)
  (V : Rules G) (hBasis : 4*(b:ℝ)*p.threshold ≤ V.c) (hn : 2*(b+1)<n.val)
  (hR : dues p b < radius G k)
  (U : Config G n) (hu : Healthy p.threshold (hull b o) U)
include hF hX hBasis hn hR hu

/-- Even at equality of the old flag threshold, this theorem on a common
healthy hull proves actual unmasked germ smoothness (not needed if a render
is supplied already Regular on a smaller support). -/
theorem toll_gate : ContDiffAt ℝ k (F ∘ increment U) 0 := by
  let W : Directions G n:= doorway o b U
  obtain ⟨hw,hb⟩ := arrival V hn hBasis o U hu
  have he : ∀ i, ‖W i‖ < radius G k := fun i => ((norm_le_pi_norm W i).trans hb).trans_lt hR
  let f := F ∘ increment (1:Config G n)
  have hh := (hF.germ W hb)
  have hj := ordered_chug (j:=1) he (by omega) (1:Config G n)
  let enter (v : Directions G n) : WardBin.Lies.Slab G n 1 := fun _ => chief (fingers U o) X v
  have hE : ContDiff ℝ ω enter:= contDiff_pi.mpr fun _ => chief_cd ..
  have h₀ : enter 0=0:= funext fun _ => chief_zero ..
  have ht : F ∘ increment U =ᶠ[nhds (0:Directions G n)] f ∘ through (siteFrame W 1) ∘ enter:= by
    have hc:= hE.continuous.continuousAt (x:=0); rw [ContinuousAt,h₀] at hc
    filter_upwards [hc.eventually hj] with v hv
    change F _=F _
    rw [chief_enters hs hl (fingers U o) (agrees_mono hw (show (X:Set (Four (Per n))) ⊆ ↑(hull b o) from fun _ hu=> hX hu))]
    apply congr_arg F
    exact hv
  refine (ContDiffAt.comp (f:=enter) _ (ContDiffAt.comp (g:=f) (f:=through (siteFrame W 1)) _ ?_ ?_) (hE.contDiffAt.of_le le_top)).congr_of_eventuallyEq ht
  · rw [h₀,initial he]; exact hh
  rw [h₀]; exact through_smooth (fun _=> (reframe (j:=1) he (by omega) _).of_le le_top)

lemma Read (x : Site n) (hx : x ∈ hull b o) (l : List (Directions G n)) (he : l.length ≤ k) (ht : ∀ i∈l, p.dirBound x i) :
    ‖leftDerivs F l U‖ ≤ balance G k r (dues p b) ε c := by
  obtain ⟨hw,hb⟩:= arrival V hn hBasis o U hu
  let f:= fingers U o
  let L:=l.map (chief f X)
  rw [paid hs hl f (agrees_mono hw (show (X:Set (Four (Per n))) ⊆ ↑(hull b o) from fun _ hu=> hX hu))]
  change ‖leftDerivs F L _‖ ≤ _
  rw [← List.ofFn_get L]
  let A : Fin L.length→ Directions G n := L.get
  have hf x : ‖(doorway o b U) x‖ < radius G k := ((norm_le_pi_norm _ _).trans hb).trans_lt hR
  apply stationed hF hb hf A _ (List.length_map _ |>.trans_le he)
  intro i; have h : A i∈L:=List.get_mem L i
  obtain ⟨y,hy,h⟩:=List.mem_map.mp h
  rw [← h]; exact chief_in _ hX x hx _ (ht _ hy)

variable [MeasurableSpace E]
include hs hl hF hX hBasis hn hR
omit hu in
/-- One common healthy hull estimate, with moving angular exponent/order
and locality/registered root intact. Needs the field price on the true small
chart. Unmasked equality of functions across a moving representative can be
established before this call; a changed pole or hull otherwise requires an
actual exponent correction at bad flags (see RG3.Forms). Suppression is
explicitly in `balance`; don't throw away the `(1+2b)^power` factors in a
Hall rate or an output iteration step. -/
theorem rent (hm : Measurable F) (hk : p.order ≤ k) :
    p.Regular (hull b o) F ∧ ∀ x∈hull b o, p.supBounds x (hull b o) F (balance G k r (dues p b) ε c):= by
  have he (U : Config G n) (hu : Healthy p.threshold (hull b o) U) := (toll_gate hs hl hF hX V hBasis hn hR U hu).of_le (Nat.cast_le.mpr hk)
  refine ⟨⟨fun A S h => hl _ _ (agrees_mono h (fun _ h=> hX h)),hm,hs,he,fun U hx i l h => Next.Foundations.left_has i h (he U hx)⟩,
    fun x hx => ⟨balance_nn G k r hF.tau hF.small hF.high,fun U hu l hh hA=> Read hs hl hF hX V hBasis hn hR U hu x hx l (hh.trans hk) hA⟩⟩
end YM.RG3.Axial
