import YM.FrontierTrace.Primary.HorizonFour

/-!
# Top scalar & spin multiplicities retained exactly through the *actual* calibration.

Uses H, not assuming all-axis mixing vanishes. `metricSource` is the grade (4,2)
raw OFFDIAG. Unit cancellation via explicit `unit_label` and correction priced later.
Works for all periods/cutoff `C.ref 4≤N`. Helps in obtaining the finite-order estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Filter Analysis Labels Maxwell Maxwell.Free Table
open UVNext.FreeStress Next.UVStress Work.A01 Trace
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical

variable {G:Gauge}
variable (C:Family G) (h:G.Simple)
local notation "L" => C.labels.level 4
local notation "D" => freeTable C.labels
local notation "Θ4" => metric0 C.labels
local notation "Σ4" => scalarLabel C.labels

/-- Label data -- used everywhere incl bare/pre-shell. -/
def scalarSource (G:Gauge) : Label G 4 := (4:ℂ)⁻¹ • ∑ i:Axis,∑ j:Axis, StressFlux.pair G i j i j
def metricSource (G:Gauge)(i j:Axis) : Label G 4 := -(∑ k:Axis, StressFlux.pair G i k j k)
def scalarKey: C.label 4 := (L).coords (scalarSource G)
def metricKey (i j:Axis) : C.label 4:= (L).coords (metricSource G i j)
lemma pairGrade (G:Gauge) (i j p q:Axis): StressFlux.pair G i j p q ∈ Grade (4,2) :=
    StressFlux.productPol_grade (StressFlux.curl0 i j) (StressFlux.curl0 p q)
lemma scalarGrade (G:Gauge): scalarSource G ∈ Grade (4,2):= Submodule.smul_mem _ _ (Submodule.sum_mem _ fun _ _=> Submodule.sum_mem _ fun _ _=> pairGrade _ ..)
lemma metricGrade (G:Gauge) (i j:Axis): metricSource G i j∈ Grade (4,2):= Submodule.neg_mem _ (Submodule.sum_mem _ fun _ _=>pairGrade _ ..)
lemma expands_metric {i j:Axis}(hv:i≠j): (D).project 4 (metricKey C i j)=metric0 C.labels i j:=by
   rw [metric0,canonicalStress, if_neg hv, sub_zero]
   unfold metricKey metricSource panel; simp_rw [← bond_at, map_neg,map_sum]; rfl
lemma expands_scalar : (D).project 4 (scalarKey C)=Σ4:=by
   change embed C.labels 4 _ = _; rw [scalar_as_total,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; unfold scalarSource total; rw [map_smul]; simp_rw [map_sum,← bond_at]; norm_num; rfl
lemma expands_unit : (D).project 4 (L).e0=(D).unit 4:=by rw [← Labels.Frame.coords_unit]; exact UVNext.FreeStress.pin_unit ..

/-- Natural isomorphism before quotient. -/
def projectEquiv : C.label 4≃ₗ[ℂ](D).Field 4:= LinearEquiv.ofBijective ((D).project 4) ⟨projected4 _ h le_rfl,(D).onto 4⟩
local notation "P₀"=> projectEquiv C h
lemma projectV (v:C.label 4): P₀ v=(D).project 4 v:= rfl
lemma project_metric (i j:Axis)(hx:i≠j): (P₀) (metricKey C i j)=metric0 C.labels i j:=expands_metric C hx
lemma project_scalar : (P₀) (scalarKey C)=Σ4:=expands_scalar C
lemma e0R : (P₀) (L).e0=(D).unit 4:= expands_unit C
-- Laurent Polo transform symm
abbrev LegOrder : Type := C.label 4≃ₗ[ℂ] C.label 4
abbrev lowL (N p:ℕ): LegOrder C := (C.factory 4 N p).terminal
local notation "Lk"=> lowL C

/-- Coherence in raw basis for top/readout transformation: actual one flavor.
Nonrescaling of unit *not* required, appears in `preservesOne`. -/
structure LegRule (t:LegOrder C) : Prop where
    signed (x: C.label 4) (g:Signed) : t ((L).act g.ortho x)= (L).act g.ortho (t x)
    real_t (x:C.label 4): t (star x)= star (t x)
    preservesOne : ∃ u:ℂ, u≠0 ∧ t (L).e0=u • (L).e0
lemma rule_symm (t:LegOrder C)(h:LegRule C t): LegRule C t.symm:=by
   obtain ⟨u,hu,hk⟩:=h.preservesOne; constructor
   · intro x g; apply t.injective; rw [h.signed]; simp only [LinearEquiv.apply_symm_apply]
   · intro x; apply t.injective; rw [h.real_t]; simp only [LinearEquiv.apply_symm_apply]
   refine ⟨u⁻¹,inv_ne_zero hu,?_⟩; apply t.injective; rw [map_smul,hk,inv_smul_smul₀ hu,LinearEquiv.apply_symm_apply]
lemma actual_rule (hc:C.Makes){N p:ℕ} (hN:C.ref 4≤ N): LegRule C (Lk N p):=by
   have h:= hc.calibrated 4 N p hN; constructor
   · intro x g; exact h.orients ..
   · intro x; exact h.realForm ..
   let b:= ((C.S.a N:ℂ)^4); let u:=((C.S.a (C.ref 4):ℂ)^4); have hb : b≠0:=pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'); have hu :u≠0:= pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'); refine ⟨b⁻¹*u,mul_ne_zero (inv_ne_zero hb) hu,?_⟩
   have hv:Lk N p (b • (L).e0) = u • (L).e0:= (h.reads _).symm.trans (h.unit_coord (C.ref 4) le_rfl hN)
   apply smul_right_injective _ hb; dsimp only; rw [smul_smul,show b*(b⁻¹*u)=u by field_simp, ← hv,map_smul]

def freeFlow (t:LegOrder C): (D).Field 4 ≃ₗ[ℂ] (D).Field 4 := ((P₀).symm.trans t).trans (P₀)
local notation "Q"=> freeFlow C h
local notation "u0"=> (spin_free C.labels)
lemma freeFlow_apply (t:LegOrder C)(x:C.label 4) : Q t ((D).project 4 x)=(D).project 4 (t x):= by
    unfold freeFlow; rw [← projectV C h x]; simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]; rfl
lemma freeFlow_real {t:LegOrder C} (H:LegRule C t): Next.UVStress.Coherent u0 u0 4 (Q t):=by
   constructor
   · intro u; obtain ⟨x,rfl⟩ := (D).onto 4 u; simp_rw [(D).conj_project,freeFlow_apply C h]; rw [(D).conj_project]; exact congr_arg ((D).project 4) (H.real_t x)
   intro g u; obtain ⟨x,rfl⟩:= (D).onto 4 u; simp_rw [(D).mirror_project,freeFlow_apply C h]; rw [(D).mirror_project]
   apply congr_arg ((D).project 4); exact H.signed x g
-- Mean is real
lemma expectF_real {x:(D).Field 4} (hx:(D).conj (spin_free C.labels) 4 x = x):
    ∃ u:ℝ, expectation D 4 x=(u:ℂ):=by
   let U:= expectation D 4 x
   have hz: (D).conj u0 4 (centering D 4 x)=centering D 4 x:= by rw [conj_center (hierarchy C.labels),hx]
   simp only [value_center,map_sub,map_smulₛₗ,(D).conj_unit,hx] at hz
   have hk:(starRingEnd ℂ) U=U:=smul_left_injective ℂ ((D).alive 4 (hierarchy C.labels).laws) (sub_right_inj.mp hz)
   exact ⟨U.re,(Complex.conj_eq_iff_re.mp hk).symm⟩
include h
lemma chart_scalar {t:LegOrder C}(H:LegRule C t) : ∃ a b:ℝ,a≠ 0 ∧ t (scalarKey C)= a • scalarKey C+b • (L).e0 := by
   let p : LegOrder C :=t; let V:= Q p
   have hP:=freeFlow_real C h H
   have hv : (D).conj u0 4 (V Σ4)=V Σ4:= by rw [←show V ((D).conj u0 4 Σ4) = _ from hP.1 _]; rw [scalar_real]
   obtain ⟨a,ha⟩:= center_fixed_dim C.labels h (v:=V Σ4) (fun g=> by rw [←show V ((D).mirror u0 4 g Σ4) = _ from hP.2 ..]; rw [scalar_signed]) hv
   obtain ⟨x,hx⟩:= expectF_real C hv; rw [value_center,hx] at ha
   have he:t (scalarKey C)= a • scalarKey C+x • (L).e0:=by
      apply (P₀).injective; have hh:=sub_eq_iff_eq_add.mp ha; rw [← project_scalar C h] at hh
      simp_rw [map_add,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]; rw [e0R,show (P₀) (t _) = V ((P₀) (scalarKey C)) from (freeFlow_apply C h ..).symm,hh,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
   refine ⟨a,x,?_,he⟩
   obtain ⟨u,hu,hk⟩:=H.preservesOne; intro hf
   have hw:(P₀) (scalarKey C)=(u⁻¹*(x:ℂ)) • ((D).unit 4):= by
      rw [← e0R C h, ← map_smul]
      apply congr_arg; apply t.injective; rw [map_smul,hk,he,hf,zero_smul,zero_add, smul_smul, show u⁻¹*(x:ℂ)*u=x by field_simp,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
   rw [project_scalar C h] at hw; apply money_ne_zero (C:=C) h; have hM : expectation D 4 Σ4=0:= by
      have he': expectation D 4 Σ4 = first_value (S:=Climb.Bel C.book) 4 Σ4 := by rw [expectation,front_eval]; unfold first_value; congr 2; funext j; fin_cases j;rfl
      exact he'.trans (mean_scalar_free (C:=C))
   rw [hw, map_smul,Next.UVStress.mean_unit (hierarchy C.labels).laws,smul_eq_mul,mul_one] at hM
   rw [hw,hM,zero_smul]

-- adapt offdiag membership function supplied generically later so avoid local F.
lemma offdiag_color (J:(D).Stress) (hm:J∈SymSpace u0): ∃ a:ℝ,∀ (i j:Axis), i≠j→ J i j= a • metric0 C.labels i j:= by
   let v:= reCenter D J
   have hv : v∈KernelSpace u0:= enters (hierarchy C.labels) _ hm
   obtain ⟨a,b,c,h⟩:=exhaust C.labels u0 h (⟨v,hv⟩:KernelSpace _)
   refine ⟨-c,fun i j hij=>?_⟩
   have heq := congr_fun (congr_fun (show v= _ from h) i) j
   change centering _ _ (J i j)= paintStress _ _ _ _ i j at heq
   simp only [paintStress, Pi.add_apply,Pi.smul_apply,UVNext.FreeStress.across,east,west,splitDiag,
      ↓reduceIte,hij,smul_zero,add_zero,zero_add] at heq
   rw [offdia_mean (C:=C) (Signed.mirror i) ?_] at heq
   rotate_left
   · rw [tensor_column (sym_mem.mp hm).2.2]
     rw [eps_mirror_bit, eps_mirror_bit]
     norm_num [hij,Ne.symm hij,UVNext.FreeStress.bit,Signed.mirror]
   rw [heq,metric0,canonicalStress,if_neg hij,sub_zero,neg_smul,smul_neg,neg_neg]
lemma chart_metric {t:LegOrder C}(H:LegRule C t) : ∃ a:ℝ, a≠ 0 ∧ ∀ (i j:Axis), i≠j→t (metricKey C i j)=a • metricKey C i j := by
    let T:= transformed (Q t) Θ4
    have ht : T∈ SymSpace u0:= by
       apply transformed_mem (freeFlow_real C h H); apply (kernel_mem.mp ?_).1
       exact (KernelSpace _).neg_mem ((lighting C.labels u0) ▸ (generator C.labels u0).property)
    obtain ⟨a,ha⟩:= offdiag_color C h T ht
    refine ⟨a,?_,?_⟩
    · intro he; specialize ha 0 1 (by decide); rw [he,zero_smul] at ha; apply metric_ne_zero C.labels h
      exact (Q t).injective (ha.trans ((map_zero _).symm))
    intro i j hi; apply (P₀).injective; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul, projectV, ← freeFlow_apply C h,projectV, expands_metric C hi]; exact (ha i j hi).trans (RCLike.real_smul_eq_coe_smul (K:=ℂ) ..)

end YM.FrontierTrace.Primary
