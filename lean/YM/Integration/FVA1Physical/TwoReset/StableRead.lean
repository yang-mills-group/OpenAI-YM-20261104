import YM.Integration.FVA1Physical.TwoReset.MarkCover
import YM.Comparison.RG02.Adjacent.Caliber

/-! Verify that MarkCover probes suffice as Wilson model identifications:
two renderings with these same probes (same marker units, unmasked stencil
convention) produce the same next formal answer. No dependence on choices of
writing the higher part/cutting within the REAL norms. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Comparison.RG02.Assembly
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G:Gauge} {V : Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Extend from t=1 probes to *all* joint coefficients, including t=0.
lemma tangent (f g : ℝ × E → F) (i:ℕ) (he : ∀ x, Assembly.jet f i (1,x) = Assembly.jet g i (1,x)) :
    Assembly.jet f i = Assembly.jet g i := by
  have hm (t:ℝ)(ht : t≠0)(x:E) : Assembly.jet f i (t,x)= Assembly.jet g i (t,x) := by
    have hx : (t,x)=t • (1,t⁻¹ • x):= Prod.ext (mul_one _).symm (smul_inv_smul₀ ht x).symm
    conv_lhs=>rw [hx,Assembly.Clipper.weight,he];
    rw [hx, Assembly.Clipper.weight]
  funext p; obtain ⟨z,x⟩:=p
  by_cases hz:z=0
  swap; · exact hm z hz x
  subst z
  have h(q:ℝ×E→F): Tendsto (fun t:ℝ=> Assembly.jet q i (t,x)) (𝓝[≠] 0) (𝓝 (Assembly.jet q i (0,x))) :=
    (((show Continuous (Assembly.jet q i) from
      (YM.Tensor.diag_smooth (Tensor.coeff q i 0) ∞).continuous).comp (f:=fun t:ℝ=> (t,x))
        (by fun_prop)).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq (h f) (h g) (by
    filter_upwards [show ∀ᶠ t:ℝ in 𝓝[≠] 0,t≠0 from self_mem_nhdsWithin] with t ht
    exact hm t ht x)

variable {c f : Side} {B : StepData c f} {P : Clip} {Y' : PathData G} {O : ChartRatio G}
variable (K : Kernel B P Y' O) (A : Forest B.ratio) (ν : B.Choices)
variable (Y Z : Colors R G f) (p:ℕ) (h0 : Y.power=Z.power)
    (hy : Well Y) (hz : Well Z)
    (he : ∀ i≤p,∀ v, Air.discharge Y i (Stationary.arm G f 1 v) =
      Air.discharge Z i (Stationary.arm G f 1 v))
    (hq : ∀ j≤p,∀ x, vacuumLetter (geometric K A ν Y) x j=vacuumLetter (geometric K A ν Z) x j)

lemma equal_delta {f g:E→F} {i:ℕ} (hf:ContDiffAt ℝ ω f 0) (hg:ContDiffAt ℝ ω g 0)
    (he : Assembly.jet f i = Assembly.jet g i) : iteratedFDeriv ℝ i f 0 = iteratedFDeriv ℝ i g 0 := by
  apply Tensor.ext_diag _ _ (YM.Analysis.sym_Jet (hf.of_le le_top)) (YM.Analysis.sym_Jet (hg.of_le le_top))
  exact funext fun x=> (smul_right_inj (show ((Nat.factorial i:ℝ)⁻¹)≠0 from by positivity)).mp
    (congr_fun he x)

include h0 hy hz he
omit [Fintype V] in
private lemma same_driver (j:Multi.Hot R)(i:ℕ)(hi:i≤p)(x : Bulk.Joint (G:=G) B A) :
    Assembly.markLetter Y.power (Bulk.markFn B A Y) j x i =
      Assembly.markLetter Z.power (Bulk.markFn B A Z) j x i := by
  let u(v:ℝ)(x:Config G f):= Y.mark j v x-Z.mark j v x
  let n := Z.power j
  have hf : projected u = projected (Y.mark j)-projected (Z.mark j):= rfl
  let hp := hy.suppose_mark j
  let ht := hz.suppose_mark j
  have hE : Assembly.GradeAt (n+p+1) (projected u) := by
    rw [hf]; constructor
    · exact hp.smooth.sub ht.smooth
    intro i h
    rw [iteratedFDeriv_sub_apply (hp.smooth.of_le le_top) (ht.smooth.of_le le_top)]
    apply sub_eq_zero.mpr
    by_cases hr:i<n
    · exact (hp.vanish i (congr_fun h0 j ▸ hr)).trans (ht.vanish i hr).symm
    apply equal_delta hp.smooth ht.smooth; refine tangent _ _ i (fun x=>?_)
    obtain ⟨v,rfl⟩:∃ v, x = (Stationary.arm G f 1) v := by
      obtain ⟨v,h⟩:= (Stationary.arm G f 1).surjective x; exact ⟨v,h.symm⟩
    obtain ⟨k,hk⟩:= Nat.exists_eq_add_of_le (Nat.le_of_not_gt hr)
    have h' := congr_arg (fun y:Poly R=> y.part j.val) (he k (by omega) v)
    change (Multi.lit R _).part j.val=(Multi.lit R _).part j.val at h' -- annotate
    simp only [part_lit,h0] at h'
    exact hk.symm ▸ h'
  have h := (Bulk.joint_receipt B A hE).vanish (n+i) (by omega)
  rw [show posed B A u = Bulk.posed B A (Y.mark j) - Bulk.posed B A (Z.mark j) from rfl,
    iteratedFDeriv_sub_apply ((Bulk.joint_receipt B A hp).smooth.of_le le_top)
      ((Bulk.joint_receipt B A ht).smooth.of_le le_top)] at h
  unfold Assembly.markLetter Assembly.jet Bulk.markFn; unfold n at h; rw [h0,sub_eq_zero.mp h]

include hq
omit h0 hy hz he in
lemma same_prescription (H:∀ (j:Multi.Hot R)(i:ℕ),i≤p → ∀ x:Bulk.Joint (G:=G) B A,
     Assembly.markLetter Y.power (Bulk.markFn B A Y) j x i=Assembly.markLetter Z.power (Bulk.markFn B A Z) j x i) (x: Exterior.fieldDir G c 1) : Bulk.Fk K A ν Y x p= Bulk.Fk K A ν Z x p := by
  let e := Embedding.refl V
  let u : Extra.Trajectories.Names R R := ⟨e,fun i=> by change i.val.image id ∈ _; simp⟩
  let q := Embedding.refl (Fin p)
  have h(i:R.Mode):u.share i=i:= by apply Subtype.ext; change i.val.image id=i.val; simp
  have h'(i : Multi.Hot R):u.look i=i:= Subtype.ext (h i.val)
  have k(j: Order.Index p): (Order.indexNames q).share j=j:= by apply Subtype.ext; change j.val.image id=j.val; simp
  have identity(y: Order.Grade R p): Order.truncate u q y=y:= by
    apply Marker.Poly.ext; intro v
    -- write v = Join.pair ...
    obtain ⟨i,j,rfl⟩ : ∃ i j,v=Order.Join.pair i j := ⟨_,_,(Order.Join.pair_reunite _).symm⟩
    rw [Order.trunc_part,h,k]
  let Y' := Bulk.Fk K A ν Y x p
  rw [← identity (Bulk.Fk K A ν Y x p)]; apply Assembly.restriction _ _ _ _ _ _ _ (K.positive A ν) u q Y.power _ _ hq
  intro i j hj x; rw [h' i]; exact H i _ hj _
lemma same_Fk (x: Exterior.fieldDir G c 1) : Bulk.Fk K A ν Y x p= Bulk.Fk K A ν Z x p := by
  exact same_prescription K A ν Y Z p hq (fun i j hj x=>same_driver A Y Z p h0 hy hz he i j hj x) x
omit hq he h0 hz hy

variable (R₁ : Run G) {t n N:ℕ} {ι μ α:Type} {V₁ V₂: Passport (R₁.family.side (t+1) n) V}
variable (hN : t<N)
variable (P₁: ι → Row V₁ R G α) (P₂: μ → Row V₂ R G α) (w: V→ℕ) (D:Layout G) (T:Finset Age)
variable {a a' : ℝ} {k k' : ℕ} (hD:Legal T D)
    (h₁:∀ t:α, Air.Staff P₁ (fun i=>(P₁ i).paint t) w a k)
    (h₂:∀ t:α, Air.Staff P₂ (fun i=>(P₂ i).paint t) w a' k')
    (hu:∀ (C:Side) (hC : (R₁.family.side (t+1) n).val ∣ C.val) (z:α),∀ i ≤ p,
      peek hC P₁ w D T z i = peek hC P₂ w D T z i)
include h₁ h₂ hD hu

lemma covered_rep_eq t' n' hX A Y x i :
    TwoReset.FkCover R₁ hN D T p P₁ w t' n' hX A Y x i=
      TwoReset.FkCover R₁ hN D T p P₂ w t' n' hX A Y x i := by
  funext y
  let h:= tiled R₁ hX y
  have Hp(k:ℕ)(hk:k≤p):= hu _ h t' k hk
  unfold TwoReset.FkCover; dsimp only
  let C₁ := copyColor h P₁ w (fun i=>(P₁ i).paint t') D T
  let C₂ := copyColor h P₂ w (fun i=>(P₂ i).paint t') D T
  let t₁ := ((RunFormalChain.fromRun R₁).step N t y hN)
  let A' := A y; let t'':=Y y
  have h₁' : Well C₁:= (copy_standard h P₁ w _ D T (h₁ t') hD).1
  have h₂' : Well C₂:= (copy_standard h P₂ w _ D T (h₂ t') hD).1
  have h := same_Fk t₁ A' t'' C₁ C₂ p rfl h₁' h₂'
    (fun i hi x=> congr_fun (Hp i hi) x) (fun i hi x=>rfl)
    (Stationary.arm G _ 1 (convey (coverWin y.prop) x))
  exact congr_arg (fun f=> (((Pages n' (R₁.family.side t y):ℕ):ℝ)⁻¹ : ℝ) •
    Order.observe R p (Order.logMarked f) i) h

/-- ALL testing periods criterion for forecast independence when starting
another RG02 call. -/
lemma reenter_same (X) : MarkCover R₁ hN D T p P₁ w X ↔ MarkCover R₁ hN D T p P₂ w X := by
  have e:= covered_rep_eq (p:=p) (R₁:=R₁) (hN:=hN) P₁ P₂ w D T hD h₁ h₂ hu
  constructor
  · intro h t n hX A Y x i hi
    rw [← e]
    exact h t n hX A Y x i hi
  intro h t n hX A Y x i hi
  rw [e]
  exact h t n hX A Y x i hi
end YM.Integration.FVA1Physical.TwoReset
