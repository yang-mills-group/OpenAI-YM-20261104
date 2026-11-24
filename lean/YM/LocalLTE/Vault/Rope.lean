import YM.LocalLTE.Concourse.Core
import YM.LocalLTE.Tol.Pack
import YM.Extra.MULTISOURCE_BOUNDS.Columns
/-!
# Offers from canonical field probes at common site

Actual section, exact stencil including gauge convention. `harvest` activates.
Radius of b may be fixed across all careers. No convergence/limit scope here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vault
open Finset Function Filter Lattice Wilson RG Source Labels Extra.Histories
open Push Local PhysicalNext.Repeat MeasureTheory ConnectedActivityE6 Blaze
open Next.Foundations Extra.Multi.BasisCost Push.AbsoluteSums Animals
open Port
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {d:ℕ}
variable (G)
def terr (d₀:ℕ):ℕ:= ∑ i∈range (d₀+1), (Port.Sect.insideL (G:=G) i).choose
lemma placeV {d D:ℕ}(h:d≤D){n:Side}(o:Site n) : (localSection G d).footprint o ⊆ neighbors (terr G D) o:=by
   intro x hx; have ht:= (Port.Sect.insideL (G:=G) d).choose_spec n o hx
   exact (neighbors_mem ..).2 (((neighbors_mem ..).1 ht).trans (single_le_sum (f:=fun i=>(Port.Sect.insideL (G:=G) i).choose) (fun i _=>Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le h))))
local notation "P'"=> localSection G
variable {G}
-- Grading evaluator, same as approach in YM/TraceExtension/Margin/Card. Proved fresh.
lemma flatPrice (T:SectionData ((Labels.frames G).level d)){H:Hol G}(hv:T.Sound H)(v:((Labels.frames G).level d).Coeff): T.evaluate v (1:CoverConfig G)=v 0:=by
   let W:= ((Labels.frames G).level d); have h := (hv.projects v (0:Jet G)).2.2 0 (Nat.zero_le _)
   simp_rw [iteratedDeriv_zero,H.flat,show scaleJet (0:Jet G) (0:ℝ)=0 from funext fun i=>smul_zero _] at h
   rw [h]; have he: W.scaled 0 v=v 0 • W.e0:=by
         funext i; by_cases hi:i=0
         · subst i; simp [W.zero_degree,Frame.e0]
         simp [Frame.e0,Pi.single_eq_of_ne hi,(W.factors_pos i hi).ne']
   have hp:= read_frame_scaled (0:Jet G) W v 0; rw [show (0:ℝ) • (0:Jet G) = 0 from zero_smul _ _,he] at hp
   rw [show _= Labels.read (0:Jet G) (W.coords.symm (v 0 • W.e0)).val from hp.symm,map_smul,← W.coords_unit,LinearEquiv.symm_apply_apply,Submodule.coe_smul,map_smul];simp [Labels.unit]
variable {n : Side} {o : Site n} {J:Type}
lemma fare_one (T:SectionData ((Labels.frames G).level d)){H:Hol G}(hv:T.Sound H)(v:((Labels.frames G).level d).Coeff)(t:ℝ) : presented T o t v (1:Config G n)= v 0:=by
    let W:= (Labels.frames G).level d; change T.evaluate (W.scaled t⁻¹ v) (1: CoverConfig G)=v 0
    rw [flatPrice T hv]; simp [W.zero_degree]
noncomputable def fareK (P:BudgetPoint)(i:J→ℕ)(k:∀ z:J, ((Labels.frames G).level (i z)).Coeff)(I: Finset J) (o:Site n): Config G n→ℂ := ∏ z∈ I,presented (localSection G (i z)) o P.threshold (k z)
variable (P: BudgetPoint)(i:J→ℕ)(k:∀ z:J, ((Labels.frames G).level (i z)).Coeff)(I: Finset J)
variable (ht:∀ z∈I, ((Labels.frames G).level (i z)).coeffSize (k z) ≤1)
local notation "p'"=> fareK P i k I
set_option quotPrecheck false
-- singleton.As well.
lemma fare_root : fareK P i k I o 1 = ∏ z∈I,k z 0:=by rw [fareK, Finset.prod_apply]; exact prod_congr rfl (fun z _=> fare_one _ (sound ..) _ _)
include ht
lemma fare_small : ‖fareK P i k I o 1‖ ≤ 1:=by
    rw [fare_root,norm_prod]; exact prod_le_one (fun i _=>norm_nonneg _) (fun i hi=> (Extra.Multi.BasisCost.coord_le (k i) 0).trans (ht _ hi))
variable (D:ℕ)(he:∀ z∈I,i z≤D)
variable (o)
variable {t:ℝ}
noncomputable def froth (u:ℝ)(p c:ℕ): ℝ:= (2^p*u)^c
set_option maxHeartbeats 250000
include he
lemma fare_good (hp:∀ z∈I,∀ j, P.Regular ((localSection G (i z)).footprint o) ((localSection G (i z)).places (Pi.single j 1) o) ∧ P.supBounds o ((localSection G (i z)).footprint o) ((localSection G (i z)).places (Pi.single j 1) o) (t*P.threshold^(((Labels.frames G).level (i z)).grades j).2)) (hu:1 ≤ t): P.Regular (neighbors (terr G D) o) (p' o) ∧ P.supBounds o (neighbors (terr G D) o) (p' o) (froth t P.order I.card):=by
   let X:= neighbors (terr G D) o
   have h (z:J) (hz:z∈I) : P.Regular X (presented (localSection G (i z)) o P.threshold (k z)) ∧ P.supBounds o X (presented (localSection G (i z)) o P.threshold (k z)) t:= by
      have hQ:= Extra.Multi.BasisCost.analytic (localSection G (i z)) P (k z) o (hp _ hz); have hY : (localSection G (i z)).footprint o⊆X:= placeV G (he _ hz) o
      exact ⟨regular_larger hQ.1 hY,bound_weaken (bound_larger hQ.2 hY) (mul_le_of_le_one_right (zero_le_one.trans hu) (ht _ hz))⟩ -- orientation reg bound
   suffices Hℓ:∀ S:Finset J,S ⊆ I→ P.Regular X (fareK P i k S o) ∧ P.supBounds o X (fareK P i k S o) (froth t P.order S.card) from Hℓ I (Finset.Subset.refl _)
   intro S
   induction S using Finset.induction_on with
   | empty => intro _; simp only [fareK,prod_empty,froth,pow_zero,card_empty]; refine ⟨regular_const (1:ℂ),?_⟩; simpa only [norm_one, pow_zero] using! bound_const (B:=P) (X:=X) (o:=o) (1:ℂ)
   | insert a s hB ih=>
      intro hh; obtain ⟨hp,hA⟩:=Finset.insert_subset_iff.mp hh; obtain ⟨hf,hc⟩:= ih hA; have h:=h _ hp
      rw [show fareK P i k (insert a s) o=presented (localSection G (i a)) o P.threshold (k a)*fareK P i k s o from prod_insert hB]; refine ⟨regular_mul h.1 hf,bound_weaken (Local.bound_mul h.1 hf h.2 hc) ?_⟩
      rw [card_insert_of_notMem hB]; unfold froth; rw [pow_succ]; exact le_of_eq (by ring)
-- whole field tariff when needed at actual K.
noncomputable def most (G:Gauge)(d:ℕ) := (Finset.range (d+1)).sup (fun i=> Extra.Multi.BasisCost.slots ((Labels.frames G).level i)) -- shorten namespace
noncomputable def widest (G:Gauge)(d:ℕ) := 1+∑ i∈ Finset.range (d+1), Extra.Multi.BasisCost.price (localSection G i)
noncomputable def wideFare (G:Gauge)(d:ℕ)(y:ℝ)(j:ℕ):ℝ:= (widest G d * y^(most G d))^j
omit he ht in
lemma wideOne (G:Gauge)(d:ℕ):1≤ widest G d:= le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>zero_le_one.trans (Extra.Multi.BasisCost.price_pos ..))) -- include he unused
include o
lemma wideB (c:ℕ)(hj:I.card≤ c)(hQ:1≤t) (hL:P.threshold⁻¹ ≤ t) : ∀ U:Config G n, ‖fareK P i k I o U‖≤ wideFare G D t c:=by
    let w:= widest G D*t^(most G D); intro V; have hv:1 ≤ w:=one_le_mul_of_one_le_of_one_le (wideOne G D) (one_le_pow₀ hQ); apply le_trans _ (show w^I.card ≤ w^c from pow_le_pow_right₀ hv hj)
    rw [fareK,Finset.prod_apply, norm_prod, show w^I.card=∏ _∈I,w from (prod_const ..).symm]; refine prod_le_prod (fun _ _=> norm_nonneg _) fun z hz=>?_
    let F:= (Labels.frames G).level (i z); have hp:=Extra.Multi.BasisCost.full_scaled (localSection G (i z)) (k z) o P.threshold_pos (show P.threshold ≤ P.threshold from le_rfl) P.threshold_le V; let a:= Extra.Multi.BasisCost.price (localSection G (i z)); have h0:= zero_le_one.trans (Extra.Multi.BasisCost.price_pos (localSection G (i z)))
    have hP:i z∈ Finset.range (D+1):=Finset.mem_range.mpr (Nat.lt_succ_of_le (he _ hz)); have hx:a ≤ widest G D:=(single_le_sum (f:=fun i=>Extra.Multi.BasisCost.price (localSection G i)) (fun _ _=>zero_le_one.trans (Extra.Multi.BasisCost.price_pos ..)) hP).trans (le_add_of_nonneg_left zero_le_one); have hK: 0 ≤ (P.threshold)⁻¹:=inv_nonneg.mpr P.threshold_pos.le
    exact hp.trans ((mul_le_of_le_one_right (mul_nonneg h0 (pow_nonneg hK _)) (ht _ hz)).trans (mul_le_mul hx ((pow_le_pow_left₀ hK hL _).trans (pow_le_pow_right₀ hQ (Finset.le_sup (f:=fun i=> Extra.Multi.BasisCost.slots ((Labels.frames G).level i)) hP))) (pow_nonneg hK _) (zero_le_one.trans (wideOne ..))))
end YM.LocalLTE.Vault
