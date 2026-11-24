import YM.OPE.Frame.System
import YM.OPE.Schemes.Rearrange
/-!
# Tensor checks: linearity and the unit on its domain
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
namespace YM.OPE.Frame
open Table
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book} {F : Spec.Final C U S}
    {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {o p : E4} (A : I → S.Tag) (d : I → ℕ)
local notation "ν" => normalizedRotations
local notation "X" => F.sector.turns
local notation "H" => F.room.kernel
local notation "ρ" => F.room.kernel.spin
local notation "P" => F.phase.transport.spots
set_option quotPrecheck false
local notation "T'" => fun u : ∀ i : I, S.Field (d i) => (fun i:I=> (⟨d i,u i⟩ : S.Tag))
namespace Scheme
variable (Z : Scheme F) (r : ℝ) (w : Row Z.rings)
private lemma named {e : Exterior C.book} {b : Bool} (K : Ortho) (v : ∀ i : I, S.Field (d i)) :
    inspect X ρ e b x (T' v) o K =
      let f := sensed S S (beside x (escorts e o K)) (beside d fun i:Fin e.n=> (e.letter i).fst); f.currySum v (readAs X ρ e b K) := by
  let A := fun i=> (⟨d i,v i⟩ : S.Tag); exact (beside_sensed (x:=beside x (escorts e o K)) (T:=S) A (n:=fun i=> (e.letter i).fst) (readAs X ρ e b K)).symm
private lemma over_investigate {V : MultipleContact.Detector S w.fst} (b : Bool) (h : admissible V x o) :
    ∃ f : MultilinearMap ℂ (fun i => S.Field (d i)) (S.Field w.fst), ∀ v, f v = investigate X ρ V b x (T' v) o := by
  let f (e : V.probes) (K : Ortho) : MultilinearMap ℂ (fun i => S.Field (d i)) (MultilinearMap ℂ (fun i : Fin e.val.n=> S.Field (e.val.letter i).fst) ℂ) := (sensed S S (beside x (escorts e.val o K)) (beside d fun i:Fin e.val.n=> (e.val.letter i).fst)).currySum
  let g (e : V.probes) (u : ∀ i, S.Field (d i)) (K : Ortho) : S.Field w.fst := inspect X ρ e b x (T' u) o K • rotatedAnswer X ρ V e b K
  have hg (e v) : Integrable (g e v) ν := inspect_live X ρ P H (h e)
  classical
  refine ⟨MultilinearMap.mk' (fun u=> investigate X ρ V b x (T' u) o) (fun u i a c=> ?_) (fun u i c a=> ?_),fun v=>rfl⟩
  · unfold investigate; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun e _ => ?_
    change (∫ K, g e _ K ∂ν) = (∫ K, g e _ K ∂ν) + ∫ K,g e _ K ∂ν
    rw [← integral_add (hg ..) (hg ..)]; apply integral_congr_ae (Eventually.of_forall (fun K=>?_)); unfold g; let B:= readAs X ρ e b K
    have he v : inspect X ρ e b x (T' v) o K = f e K v B := named d K v
    rw [he,he,he,(f e K).map_update_add, add_apply,add_smul]
  unfold investigate; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun e _=>?_ ; rw [← integral_smul]
  apply integral_congr_ae (Eventually.of_forall (fun K=>?_)); let B:= readAs X ρ e b K
  have he v : inspect X ρ e b x (T' v) o K = f e K v B := named d K v
  rw [he,he,(f e K).map_update_smul,smul_apply,smul_assoc]

lemma by_tensor (h : Seen r x o) : ∃ f : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ, ∀ v, f v= Z.coeff r w (T' v) x o := by
  unfold coeff; by_cases hr : r < (threshold (Z.sampling w.fst))^2
  swap; · exact ⟨0,fun v=> by rw [switched _ hr]; simp⟩
  obtain ⟨f,hf⟩ := over_investigate d Z w false (gate_fitted (Z.sampling w.fst) hr.le h)
  obtain ⟨g,hg⟩ := over_investigate d Z w true (gate_fitted (Z.sampling w.fst) hr.le h)
  refine ⟨(gate (Z.sampling w.fst) r : ℂ) • ((Z.representation.coord w w.fst).compMultilinearMap ((1/2:ℂ) • (f+g))),fun v=>?_⟩
  unfold assess; rw [← hf,← hg]; rfl

private lemma drop_unit (H' : S.Hierarchy) {x : I → E4} (h : Injective (beside (sole p) x)) (k : ℕ) (A : I → S.Tag) :
    sense S (beside (sole p) x) (beside (sole (⟨k,S.unit k⟩ : S.Tag)) A) = sense S x A := by
   let B := deploy ∘ A; rw [show beside (sole (⟨k,S.unit k⟩ : S.Tag)) A = S.classTokens ∘ beside (sole (C.book.one k)) B from by
     funext i; rcases i with i|i; · rfl
     simp [B], as_token _ H'.laws.toSymmetric (fun _=>le_rfl) h]; exact local_one_mem S k B x H'.laws h

lemma as_identity (A : I → S.Tag) (h : Seen r (beside (sole p) x) o) (k : ℕ) :
    Z.coeff r w (beside (sole (⟨k,S.unit k⟩ : S.Tag)) A) (beside (sole p) x) o = Z.coeff r w A x o := by
  unfold coeff; by_cases hr : r < (threshold (Z.sampling w.fst))^2; swap; · simp [switched _ hr]
  let V := Z.sampling w.fst
  have he (e : (Z.sampling w.fst).probes) (b : Bool) (K : Ortho) : inspect X ρ e b (beside (sole p) x) (beside (sole (⟨k,S.unit k⟩ : S.Tag)) A) o K = inspect X ρ e b x A o K := by
    let B:= counted X ρ e b K; let y:= escorts e.val o K; let E := Equiv.sumAssoc Unit I (Fin e.val.n)
    let W:=beside (sole p) (beside x y); let A' := beside (sole (⟨k,S.unit k⟩ : S.Tag)) (beside A B)
    have hv: W ∘ E = beside (beside (sole p) x) y := funext fun i=> by rcases i with (i|i)|i <;> rfl
    have hp : Injective W := by
      have hh : Injective (W ∘ E) := hv.symm ▸ gate_fitted (Z.sampling w.fst) hr.le h e K
      intro i j hij; obtain ⟨i,rfl⟩ := E.surjective i; obtain ⟨j,rfl⟩ := E.surjective j; exact congrArg E (hh (show (W ∘ E) i = _ from hij))
    unfold inspect; rw [show beside (beside (sole (⟨k,S.unit k⟩ : S.Tag)) A) B = A' ∘ E from funext fun i=> by rcases i with (i|i)|i <;> rfl, ← hv,same_read A' E (F.room.kernel.laws.toSymmetric) hp]
    exact drop_unit H hp k _
  unfold assess investigate; simp_rw [he]
end Scheme
end YM.OPE.Frame
