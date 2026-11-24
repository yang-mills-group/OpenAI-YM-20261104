import YM.MergeProof.North.Tan
import YM.Integration.FundedIntrinsicProduct

/-! Finite complex combinations of booked full Wilson densities on one
original run, including their forced histories and their intrinsic reports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicProductLinearity
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels
open Extra.Histories Trace.Physical Trace.Physical.GermGraph RG16.Literal Push GridApprox MergeProof
open scoped Topology BigOperators Classical
variable {G : Gauge} (C : Family G) (N p d b : ℕ) {I : Type} [Fintype I]

omit [Fintype I] in
/-- Finite Wilson push in the original transition kernels, as in
`RG16.Bank.Dispatch`. -/
private theorem push_sum {k m : ℕ} (g : I → Config G (C.side m p) → ℂ)
    (hg : ∀ u, Integrable (g u) (prior G _)) (hi : k ≤ m) (x : Finset I) :
    pushTo C.path N p hi (∑ u ∈ x, g u) = ∑ u ∈ x, pushTo C.path N p hi (g u) := by
  induction m, hi using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    simp_rw [pushTo_next C.path N p hm, Float.push_list g hg x (C.path.levels.transition_mass ..)]
    exact ih _ fun u => StepData.push_integrable (C.path.levels.transition_mass ..) _ (hg u)

private theorem push_scalar {k m : ℕ} (g : Config G (C.side m p) → ℂ)
    (hg : Integrable g (prior G _)) (hi : k ≤ m) (x : ℂ) :
    pushTo C.path N p hi (x • g) = x • pushTo C.path N p hi g := by
  induction m, hi using Nat.le_induction with
  | base => simp
  | succ m hm ih => simp only [pushTo_next C.path N p hm, StepData.push_smul _ _ _ _ hg,
      ih _ (StepData.push_integrable (C.path.levels.transition_mass ..) _ hg)]

section Pages
variable (C : Family G) (d N m p : ℕ) {ι : Type}
local notation "F" => C.labels.level d
local notation "R" => C.path.rep N p m

/-- Coordinate projection of the actual finite merged history, following
`RG16.Address.Page` on the common germ. -/
private lemma scaled_page (u:store C d p m)(z:ℂ){r:ℝ}(hp:C.Makes)(hi:C.ref d ≤ m)(hN:m ≤ N)(h:reads d N p m u r):
  page d p m (stretch z u)=z • page d p m u:=by
   have he : (R).p=plank C m:=(hp.wilson.represents _ _ _ hN).vac
   have hg := fun v : ℂ =>stretch_format v h.1; have hS:= Germ.linear_projection F C.params  (o:=0) (fun z:ℂ=> stretch z u) (dimensions d N p m hp hi hN).1 (dimensions d N p m hp hi hN).2 (fun i=>hg i) (fun t=>⟨_,_,stretch_rem t h.2⟩) ⟨⟨fun i j=>add_smul _ _ _,fun i j=>mul_smul ..⟩,⟨fun i j=>add_smul ..,fun i j=>mul_smul ..⟩⟩
   simpa only [he,smul_eq_mul,mul_one,show stretch 1 u=u by simp [stretch],page] using hS.map_smul (c:=z) (1:ℂ)
private lemma sum_page [Fintype ι] [Nonempty ι] (X:ι→ store C d p m) {r:ι→ℝ}(hp:C.Makes)(hi:C.ref d ≤ m)(hN:m ≤ N)(h:∀ i,reads d N p m (X i) (r i)):
   page d p m (Extra.Histories.merge (code _) X)= ∑ i,page d p m (X i):=by
   let M:= Extra.Histories.merge (code _) X
   let V:= Germ.vector F C.params (plank C m).threshold (0:Site (C.side m p))
   let T (i:ι×ℕ):= V ((X i.1).regular i.2)
   have he:= hp.wilson.represents N p m hN|>.vac
   have hv (i:ι):Summable (Function.curry T i):=by simpa only [Function.curry,T,V,he] using! Germ.vector_summable F C.params (h i|>.1) (h i|>.2) (dimensions d N p m hp hi hN).1 (dimensions d N p m hp hi hN).2
   have hT:Summable T:=Summable.of_norm (summable_prod_of_nonneg (fun i=>norm_nonneg _) |>.mpr ⟨fun i=> (hv i).norm,Summable.of_finite⟩)
   have hs := (code ι).tsum_eq T; rw [hT.tsum_prod' hv, tsum_fintype (β:=ι)] at hs
   unfold page Germ.projection; rw [show (Extra.Histories.merge (code _) X).x= ∑ i,(X i).x from tsum_fintype _, show ∑' i,V (M.regular i)= _ from hs]
   rw [Finset.sum_add_distrib]
end Pages

/-- The literal normalized credit distributes through the finite complex
sum using the same bare Wilson action in every summand. -/
theorem credit_sum (hi : b ≤ N) (w : I → ℂ) (f : I → Cut C N p)
    (hf : ∀ u, Continuous (f u)) :
    credit C N p d (∑ u, w u • f u) b hi = ∑ u, w u • credit C N p d (f u) b hi := by
  let fields (u : I) : Cut C N p := fun V => (bare (C.beta N p) V : ℂ) * f u V
  have integrable (u : I) : Integrable (fields u) (prior G (C.side N p)) :=
    ((Complex.continuous_ofReal.comp (bare_cont ..)).mul (hf u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have terms : (fun V => (bare (C.beta N p) V : ℂ) * ((∑ u, w u • f u) V)) =
      ∑ u, w u • fields u := by
    funext V
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, fields]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold credit
  rw [terms, push_sum C N p (fun u => w u • fields u)
    (fun u => (integrable u).smul (w u)) hi Finset.univ, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [push_scalar C N p (fields u) (integrable u) hi (w u), smul_comm]

/-- The true canonical report is complex linear on finite booked original
densities. A merged coefficient books all forced and regular partners. -/
theorem booked_sum [Nonempty I] (H : C.Makes) (ho : Opened C d b p) (hi : b ≤ N)
    (w : I → ℂ) (f : I → Cut C N p) (hf : ∀ u, Continuous (f u))
    (hb : ∀ u, Booked C N p d (f u) b hi) :
    Booked C N p d (∑ u, w u • f u) b hi ∧
      topReport C N p d H b ho hi (∑ u, w u • f u) =
        ∑ u, w u • topReport C N p d H b ho hi (f u) := by
  choose Q r hread heq using hb
  let Qw (u : I) := stretch (w u) (Q u)
  let total := Extra.Histories.merge (code I) Qw
  have hu (u : I) : reads d N p b (Qw u) (‖w u‖ * r u) :=
    ⟨stretch_format _ (hread u).1, stretch_rem (w u) (hread u).2⟩
  have hsafety : 0 < safety C b := Real.sqrt_pos.mpr (forcedPos C.path.levels b)
  have htotal : reads d N p b total (∑ u, ‖w u‖ * r u) := by
    refine ⟨merge_format _ _ (fun u => (hu u).1), ?_⟩
    simpa only [tsum_fintype] using (merge_budget (code I) Qw hsafety
      (fun u => (hu u).2) Summable.of_finite).1
  have hval : value (C:=C) d N p b total = ∑ u, w u • value (C:=C) d N p b (Q u) := by
    funext V
    have hx := (merge_density (code I) Qw hsafety (H.wilson.represents _ _ _ hi).good
      (fun u => (hu u).2) Summable.of_finite Summable.of_finite (C.localSection d) V).tsum_eq
    rw [tsum_fintype] at hx
    rw [Finset.sum_apply]
    exact hx.symm.trans (Finset.sum_congr rfl fun u _ =>
      stretch_density (C.localSection d) (C.path.rep N p b) 0 (w u) (Q u) V)
  have hc : credit C N p d (∑ u, w u • f u) b hi = value (C:=C) d N p b total := by
    rw [credit_sum C N p d b hi w f hf, hval]
    exact Finset.sum_congr rfl fun u _ => congr_arg (fun y => w u • y) (heq u)
  refine ⟨⟨total, _, htotal, hc⟩, ?_⟩
  have hp : readPage C N p d (∑ u, w u • f u) b hi = ∑ u, w u • readPage C N p d (f u) b hi := by
    rw [readPage_eq C N p d _ H hi ho.post total htotal hc]
    apply (sum_page C d N b p Qw H ho.post hi hu).trans
    apply Finset.sum_congr rfl
    intro u _
    rw [readPage_eq C N p d (f u) H hi ho.post (Q u) (hread u) (heq u)]
    exact scaled_page C d N b p (Q u) (w u) H ho.post hi (hread u)
  simp only [topReport, hp, map_sum, map_smul]

/-- The stage chart pays the absolute coordinate sum of a whole signed
combination of calibrated displacements. -/
theorem cost_sum (H : C.Makes) (ho : Opened C d b p) (hi : b ≤ N)
    (w : I → ℂ) (v : I → C.label d) :
    mCost C d N p b (∑ u, w u • v u) ≤ ∑ u, ‖w u‖ * mCost C d N p b (v u) := by
  let A := fitting d N p b H ho hi
  change (C.labels.level d).coeffSize (A (∑ u, w u • v u)) ≤
    ∑ u, ‖w u‖ * (C.labels.level d).coeffSize (A (v u))
  simp only [map_sum, map_smul, Frame.coeffSize, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans_eq
    (Finset.sum_congr rfl fun u _ => norm_smul (w u) ((A (v u)) i))

/-- A paid basis controls the intrinsic report of the original complete
complex combination against the same weighted sum of physical labels. -/
theorem report_gap [Nonempty I] (H : C.Makes) (ho : Opened C d b p) (hi : b ≤ N)
    (w : I → ℂ) (f : I → Cut C N p) (z : I → C.label d) (e : I → ℝ)
    (hf : ∀ u, Continuous (f u)) (hb : ∀ u, Booked C N p d (f u) b hi)
    (he : ∀ u, mCost C d N p b (topReport C N p d H b ho hi (f u) -
      (C.factory d N p).terminal.symm (z u)) ≤ e u) :
    mCost C d N p b (topReport C N p d H b ho hi (∑ u, w u • f u) -
      (C.factory d N p).terminal.symm (∑ u, w u • z u)) ≤ ∑ u, ‖w u‖ * e u := by
  rw [(booked_sum C N p d b H ho hi w f hf hb).2, map_sum, ← Finset.sum_sub_distrib]
  simp_rw [map_smul, ← smul_sub]
  exact (cost_sum C N p d b H ho hi w _).trans (Finset.sum_le_sum fun u _ =>
    mul_le_mul_of_nonneg_left (he u) (norm_nonneg _))

end YM.Integration.IntrinsicProductLinearity
