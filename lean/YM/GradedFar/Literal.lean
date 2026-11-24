import YM.GradedFar.Lay
import YM.GradedFar.Indices
/-!
# Constant reference version of `m_N` on the run

Use the same period, mesh, inputs and actual Wilson ensemble. Enforce literal
reference unit on unused slots. No claim that this determines any additional W-estimator
or twist realization. Supplementary step toward G9.ii gives paired-tail prices for these reads.
Important precision and asymptotic order of length/volume stated there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Spec
open FullVolume
open Table PhysMS Trace.Pilot OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Dframe FVA2.O.Score FVA2.O.Enh FVA2.GradedFar
open Metric
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(F:Final C f S) (J:ℝ→tower S)
-- use once for all reads (R, C). may always price this lift. Not using covariance of appearances on link coordinates.
private def pole (d:ℕ) : S.Field d→ₗ[ℂ]ℂ := (Module.Projective.exists_dual_eq_one ℂ (S.alive _ F.room.kernel.laws)).choose
lemma pole_test (d:ℕ): pole F d (S.unit d)=1:= (Module.Projective.exists_dual_eq_one ℂ (S.alive _ F.room.kernel.laws)).choose_spec

def constantSection (d:ℕ) : S.Field d →ₗ[ℂ] C.book.Ref d :=
    S.representative d + (pole F d).smulRight (C.refUnit d-S.representative d (S.unit d))
lemma line_project (d:ℕ)(v:S.Field d): S.project d (constantSection F d v)=v:= by
 rw [constantSection,LinearMap.add_apply, LinearMap.smulRight_apply,map_add, S.rep,map_smul,map_sub,S.rep, show S.project d (C.refUnit d)= S.unit d from rfl,sub_self, smul_zero,add_zero]
lemma line_unit (d:ℕ): constantSection F d (S.unit d)=C.refUnit d:= by rw [constantSection, LinearMap.add_apply,LinearMap.smulRight_apply, pole_test,one_smul]; abel -- a+(b-a)
-- actual projection on shelf, for every field length incl smaller or larger r or s used
variable {n p q N m:ℕ} {d:Fin n→ℕ}
def call (d:ℕ)(r:ℝ): Sec G d →ₗ[ℂ] C.book.Ref d := (constantSection F d).comp (assign J r d).toLinearMap

lemma call_one (hC:C.Makes)(r:ℝ)(hq:C.ref p ≤ N)(hp:assign J r p (leaf G p)= S.unit p)(x: Lattice.Site (C.side N m)):
    C.O N m (d:=p) (call F J p r (leaf G p)) x=1:= by
 rw [show call F J p r _= C.refUnit p from Eq.trans (congrArg (constantSection F p) hp) (line_unit F p)]; exact C.constant hC p hq _
-- cutoff correlations `m_N` genuine constant-reference. This multilinear read exposed.
def assemble (L:Fin n→ℝ) (d:Fin n→ℕ)(N p:ℕ)(s:Lattice.Site (C.side N p))(x:Positions n):=
    (C.ensemble (N:=N) (p:=p) d (fun i=> wrap _ (x i)+s)).compLinearMap (fun i=> call F J _ (L i))
def names (L:Fin n→ℝ)(u:AppointedH140Inputs G d): Fin n→C.book.Token := fun i=>⟨d i,call F J _ (L i) (u i)⟩
lemma assembled (L:Fin n→ℝ)(s:Lattice.Site (C.side N p))(x:Positions n)(u:AppointedH140Inputs G d): assemble F J L d N p s x u=
    C.numeric N p (names F J L u) (fun i=> wrap _ (x i)+s):= rfl
lemma really (L:Fin n→ℝ)(s:Lattice.Site (C.side N p))(x:Positions n)(u:AppointedH140Inputs G d): assemble F J L d N p s x u=
    (partition G (C.side N p) (C.beta N p):ℂ)⁻¹ * ∫ U, (bare (C.beta N p) U:ℂ) * ∏ i, C.O N p (d:=d i) (call F J (d i) (L i) (u i)) (wrap _ (x i)+s) U ∂prior G (C.side N p):= by
    rw [assembled,C.num]; exact moment_formula _ _ (C.integrableR (names F J L u) (N:=N) (p:=p) (fun i=> wrap _ (x i)+s))
lemma exactCenter (hC:C.Makes) (u:AppointedH140Inputs G d)(hs:∀ i,C.ref (d i) ≤ N)(x:Positions n)(L:Fin n→ℝ)
    (y:Lattice.Site (C.side N p)): assemble F J L d N p y x u= C.numeric N p (names F J L u) (wrap _ ∘ x):= by
 rw [assembled]; exact C.anchored hC _ hs y _
lemma exact_units {d:Fin 0→ℕ}(x:Positions 0)(L:Fin 0→ℝ)(u:AppointedH140Inputs G d)(s:Lattice.Site (C.side N p)): assemble F J L d N p s x u=1:= by rw [assembled,C.num]; simp

-- continuum in *physical units*, all S. (translation lifted later). Note different L (use field changes with factor T^height costs).
def nl (d:Fin n→ℕ)(L:Fin n→ℝ)(x:Points n):= (S.classMoment S d x).compLinearMap (fun i=> (assign J (L i) (d i)).toLinearMap)

lemma unwrapped (u:AppointedH140Inputs G d)(x:Points n)(hx:x∈conf n)(L:Fin n→ℝ): nl J d L x u= S.read x (names F J L u):= by
 let A(i):=(call F J (d i) (L i) (u i)); have h:= S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d hx A
 change S.classMoment S d x (fun i=> assign J (L i) (d i) (u i)) = _; simp_rw [A,call,LinearMap.comp_apply,line_project] at h; exact h
-- panel all positions uniform budget on bounded fields. every Origin even unaligned at that p. reads physical m_N at wrap+s.
variable {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)(hF:FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
set_option linter.unusedVariables false in
def Awarded (d:Fin n→ℕ)(N p:ℕ) : Prop:=∀ i,C.ref (d i) ≤ N
lemma early (d:Fin n→ℕ): ∀ᶠ p:ℕ×ℕ in (again f).fuse,Awarded (C:=C) d p.1 p.2:=by
 rw [Order.fused]; exact Eventually.of_forall (fun i=>((eventually_all.mpr (fun i=> eventually_ge_atTop (C.ref (d i)))) : ∀ᶠ x in atTop,∀ i,C.ref (d i) ≤ x))

include hF hp hK hx hC
theorem unselected_fixed (d:Fin n→ℕ)(L:Fin n→ℝ)(ε:ℝ)(he:0<ε):
    ∀ᶠ p:ℕ×ℕ in (again f).fuse, Awarded (C:=C) d p.1 p.2 ∧ ∀ s, ∀ x:Positions n, Order.grid C p.1 x∈K → ∀ u:AppointedH140Inputs G d,Box u 1 →
      ‖assemble F J L d p.1 p.2 s x u-nl J d L (Order.grid C p.1 x) u‖≤ε:= by
 let δ:= ε/((Fintype.card (Picks G d):ℝ)+1); have hδ:0<δ:=by dsimp only [δ]; positivity
 filter_upwards [early (C:=C) (f:=f) d,eventually_all.mpr (fun i:Picks G d=> full F hF hp (names F J L (basisWord i)) hK hx δ hδ)] with
    p H h
 refine ⟨H,fun s x hx' u hu=>?_⟩; let z:=Order.grid C p.1 x; let D:=assemble F J L d p.1 p.2 s x - nl J d L z; change ‖D u‖≤ε
 have he' (i:Picks G d): ‖D (basisWord i)‖ ≤ δ:= by unfold D; rw [_root_.sub_apply, exactCenter F J hC _ H, unwrapped F J _ z (hx hx')]; exact h i _ hx'
 rw [basis_sum D u]; refine (norm_sum_le ..).trans ?_
 calc _≤ ∑ _i:Picks G d,δ:= Finset.sum_le_sum (fun i _=>by rw [norm_smul]; exact (mul_le_mul ((multipliers_le zero_le_one _ _ hu).trans_eq (one_pow _)) (he' i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      _≤ _:= by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; have hv:ε=δ*((Fintype.card (Picks G d):ℝ)+1):= by unfold δ; field_simp
                linarith
end YM.Integration.GradedFar.Auth
