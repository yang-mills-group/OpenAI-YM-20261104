import YM.RG.History
/-!
The paired top and one-step-coarser law. Keep ALL latent tags and a common
V in the read of multi-insertions/conditioning tests. Average at the actual
bare coupling; we won't need estimates against each *fixed* V in this route.
-/
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 800000
namespace YM.AveragedStep

open Filter MeasureTheory Function Lattice RG Wilson
open scoped Topology BigOperators

section admissible
-- Retain only finiteness so we can even write the moment of the observable;
-- all uniform costs will be separate. Don't use this `Envelope.cost` as a
-- price when sizes/couplings vary!
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {f : X → ℝ}
lemma env_comp (h : Envelope f) {g : Y → X} (hg : Measurable g) :
    Envelope (fun y => f (g y)) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨h.meas.comp hg, C, fun y=>H _⟩
lemma env_abs (h : Envelope f) : Envelope (fun x => |f x|) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨(continuous_abs.measurable.comp h.meas), C, fun x=>by simpa using H x⟩
lemma env_npow (h : Envelope f) (m : ℕ) : Envelope (fun x => f x ^ m) := by
  induction m with
  | zero => simpa using Envelope.const (V:=X) 1
  | succ m ih => simpa only [pow_succ] using ih.mul h
lemma env_product {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) (h : ∀ i∈s, Envelope (f i)) :
    Envelope (fun x=> ∏ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simpa using Envelope.const (V:=X) 1
  | insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (h i (by simp)).mul (ih (fun j hj=> h j (by simp [hj])))
lemma env_continuous {A : Type*} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] {f : A → ℝ} (h : Continuous f) : Envelope f :=
  ⟨h.measurable, by
    obtain ⟨C,H⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuousOn
    exact ⟨C, fun x=>H _ (Set.mem_univ x)⟩⟩
end admissible

variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)

abbrev Board (G : Gauge) (c f : Side) := Config G f × Config G c
abbrev Query (S : StepData c f) (G : Gauge) := S.Choices → Board G c f → ℝ

variable {S} in
def Admits (F : Query S G) := ∀ i, Envelope (F i)
variable {S}
namespace Admits
variable {q r : Query S G}
lemma one : Admits (1 : Query S G) := fun _ => Envelope.const 1
lemma const (k : ℝ) : Admits (S:=S) (G:=G) fun _ _ => k := fun _ => Envelope.const k
lemma add (h : Admits q) (g : Admits r) : Admits (q+r) := fun i => (h i).add (g i)
lemma neg (h : Admits q) : Admits (-q) := fun i=> (h i).neg
lemma mul (h : Admits q) (g : Admits r) : Admits (q*r) := fun i => (h i).mul (g i)
lemma abs (h : Admits q) : Admits (fun i x => |q i x|) := fun i => env_abs (h i)
lemma scale (h : Admits q) (k : ℝ) : Admits (k • q) := fun i => (Envelope.const k).mul (h i)
lemma npow (h : Admits q) (k : ℕ) : Admits (fun i x=> q i x ^ k) := fun i => env_npow (h i) k
lemma sum {ι : Type*} (s : Finset ι) (q : ι → Query S G) (h : ∀ i∈s, Admits (q i)) :
    Admits (fun k x => ∑ i∈s,q i k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (G:=G) (S:=S) 0
  | insert i s hi ih =>
    intro k; simpa only [Finset.sum_insert hi] using
      (show Envelope _ from h i (by simp) k).add (ih (fun j hj => h j (by simp [hj])) k)
lemma product {ι : Type*} (s : Finset ι) (q : ι → Query S G) (h : ∀ i∈s, Admits (q i)) :
    Admits (fun k x=>∏ i∈s,q i k x) := fun k=>env_product s _ (fun i hi=> h i hi k)
end Admits

variable (S)
/- use real throughout the new calculation; recurse all real and imaginary
coordinates separately at matching. Note: integral, not essSup in V. -/
def weightQ (i : S.Choices) (x : Board G c f) :=
  S.likelihood x.1 i * S.noise β (S.prediction x.1 i) x.2

def readQ (q : Query S G) : ℝ := ∑ i, ∫ x:Board G c f, weightQ S β i x * q i x
    ∂(law G f β).prod (prior G c)

lemma weight_pos (i : S.Choices) (x : Board G c f) : 0 ≤ weightQ S β i x :=
  mul_nonneg (S.likelihood_pos ..) (Finset.prod_nonneg fun _ _=>
    mul_nonneg (inv_nonneg.mpr (S.penaltyZ_pos _).le) (Real.exp_pos _).le)
variable (hS : S.patch.Branches S.kernel G)
include hS
lemma weight_env (i : S.Choices) : Envelope (weightQ S (G:=G) β i) := by
  have h : Envelope fun x:Board G c f=> S.likelihood x.1 i :=
    ⟨(S.likelihood_meas hS i).comp measurable_fst,1, fun x=>by
      rw [Real.norm_of_nonneg (S.likelihood_pos ..)]
      exact (Finset.single_le_sum (f:=S.likelihood x.1)
        (fun j _ => S.likelihood_pos ..) (Finset.mem_univ i)).trans_eq (S.chosen hS _)⟩
  have hh := env_comp (env_continuous (S.noise_cont (G:=G) β))
    (g:=fun x:Board G c f=> (S.prediction x.1 i,x.2))
    (((S.prediction_meas hS i).comp measurable_fst).prodMk measurable_snd)
  exact h.mul hh

variable {q r : Query S G}
lemma read_safe (h : Admits q) (i) :
    Integrable (fun x:Board G c f=>weightQ S β i x * q i x) ((law G f β).prod (prior G c)) :=
  ((weight_env S β hS i).mul (h i)).integrable _
lemma read_add (h : Admits q) (g : Admits r) : readQ S β (q+r) = readQ S β q+readQ S β r := by
  unfold readQ; simp only [Pi.add_apply,mul_add,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _=> integral_add (read_safe S β hS h i) (read_safe S β hS g i)
lemma read_fin_sum {ι : Type*} (s : Finset ι) (F : ι → Query S G) (h : ∀ i∈s, Admits (F i)) :
    readQ S β (fun k x=> ∑ i∈s,F i k x)=∑ i∈s,readQ S β (F i) := by
  unfold readQ; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _=>integral_finsetSum _ fun k hk=> read_safe _ _ hS (h k hk) i)
lemma read_le (h : Admits q) (g : Admits r)
    (he : ∀ i x, S.likelihood x.1 i ≠ 0 → q i x ≤ r i x) :
    readQ S β q ≤ readQ S β r := by
  unfold readQ
  apply Finset.sum_le_sum; intro i _
  apply integral_mono (read_safe S β hS h i) (read_safe S β hS g i)
  intro x; by_cases hv : S.likelihood x.1 i=0
  · simp [weightQ,hv]
  exact mul_le_mul_of_nonneg_left (he i x hv) (weight_pos ..)

lemma read_order (h : Admits q) :
    readQ S β q = ∑ i, ∫ U, S.likelihood U i * ∫ V, S.noise β (S.prediction U i) V * q i (U,V)
      ∂prior G c ∂law G f β := by
  unfold readQ
  refine Finset.sum_congr rfl fun i _=>?_
  rw [integral_prod _ (read_safe S β hS h i)]; simp only [weightQ,mul_assoc,integral_const_mul]

-- convenience; formula integrating coarse second for EVERY fine point
set_option synthInstance.maxHeartbeats 160000 in
lemma inner_safe (h : Admits q) (i) : Envelope (fun U:Config G f=>∫ V,S.noise β (S.prediction U i) V*q i (U,V) ∂prior G c) := by
  let F (x:Board G c f) := S.noise β (S.prediction x.1 i) x.2 * q i x
  have hh := env_comp (env_continuous (S.noise_cont (G:=G) β))
    (g:=fun x:Board G c f=> (S.prediction x.1 i,x.2))
    (((S.prediction_meas hS i).comp measurable_fst).prodMk measurable_snd)
  have he : Envelope F := hh.mul (h i)
  obtain ⟨C,H⟩ := he.cost
  refine ⟨he.meas.stronglyMeasurable.integral_prod_right'.measurable,C,fun U=>?_⟩
  exact (norm_integral_le_of_norm_le (μ:=prior G c) (f:=fun V:Config G c => F (U,V)) (g:=fun _=>C) (integrable_const _) (Eventually.of_forall fun V=> H (U,V))).trans_eq (by simp)

lemma read_one : readQ S β (1 : Query S G)=1 := by
  rw [read_order S β hS Admits.one]; simp only [Pi.one_apply,mul_one,S.noise_mass]
  have hp i : Envelope fun U:Config G f=> S.likelihood U i :=
    ⟨S.likelihood_meas hS i, 1, fun U=>by
      rw [Real.norm_of_nonneg (S.likelihood_pos ..)]
      exact (Finset.single_le_sum (f:=S.likelihood U)
        (fun j _=> S.likelihood_pos ..) (Finset.mem_univ i)).trans_eq (S.chosen hS U)⟩
  rw [← integral_finsetSum _ (fun i _=> (hp i).integrable (law G f β))]
  simp_rw [S.chosen hS]; simp

omit hS in
lemma read_scale (k : ℝ) : readQ S β (k • q) = k*readQ S β q := by
  unfold readQ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_
  rw [← integral_const_mul]; apply integral_congr_ae
  filter_upwards with x; change _*(k*_)=k*(_*_); ring
lemma read_number (k : ℝ) : readQ S β (fun (_:S.Choices) (_:Board G c f)=>k)=k := by
  rw [show (fun (_:S.Choices) (_:Board G c f)=>k)=k • (1:Query S G) from ?_,read_scale,read_one _ _ hS,mul_one]
  funext; exact (mul_one k).symm

lemma read_nonneg (h : Admits q) (he : ∀ i x,S.likelihood x.1 i≠0 → 0 ≤ q i x) :
    0 ≤ readQ S β q := (read_number S β hS 0).symm.le.trans
    (read_le S β hS (Admits.const 0) h he)
lemma read_equal (h : Admits q) (g : Admits r)
    (he : ∀ i x,S.likelihood x.1 i≠0 → q i x = r i x) : readQ S β q=readQ S β r :=
  le_antisymm (read_le S β hS h g (fun i x hv=>(he i x hv).le))
    (read_le S β hS g h (fun i x hv=>(he i x hv).symm.le))

lemma read_fine_marginal {H : Config G f → ℝ} (h : Envelope H) :
    readQ S β (fun _ x=>H x.1)=∫ U,H U ∂law G f β := by
  have he : Admits (S:=S) (fun _ x => H x.1) := fun _=> env_comp h measurable_fst
  rw [read_order S β hS he]
  simp_rw [integral_mul_const, S.noise_mass,one_mul]
  have hp i : Envelope fun U:Config G f=> S.likelihood U i :=
    ⟨S.likelihood_meas hS i,1, fun U=>by
      rw [Real.norm_of_nonneg (S.likelihood_pos ..)]
      exact (Finset.single_le_sum (f:=S.likelihood U)
        (fun j _=> S.likelihood_pos ..) (Finset.mem_univ i)).trans_eq (S.chosen hS U)⟩
  rw [← integral_finsetSum _ (fun i _=> ((hp i).mul h).integrable (law G f β))]
  simp_rw [← Finset.sum_mul, S.chosen hS,one_mul]
end YM.AveragedStep
