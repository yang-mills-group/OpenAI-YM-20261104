import YM.FormalOPE.RG10.GaugeGear.Budget
import YM.FormalOPE.RG10.Transit.Turn
/-!
 # Budget episode in a compatible normalized slab. Cover/circle grammar in mathematical
 manuscript native-rescaling and lower-capped physical distances or any approved monotone family.
 Does not identify any gauge representative for which the schedule is affordable.
 Every cost is a primitive, then one triangular result; no nested WarTag here. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open Route HStein Transit Function PowerSeries Finset
open scoped Topology BigOperators Classical

/-- Earlier terms; including at terminating constant emissions. -/
abbrev stairs (r d:ℕ) (x:Grade) := (items r d).filter fun i=> strictHop i x
abbrev upstairs (r d:ℕ):= (items r d).filter (fun i=> 0 < i.2)
lemma staid {r d x} : stairs r d x ⊆ upstairs r d := fun _ hi=> mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.1⟩
def leverage (r d:ℕ) (u:Grade):= u.1*(d+3*r+1)+(d+3*r-u.2)
def loft (r d:ℕ):= (r+1)*(d+3*r+1)
lemma cost_order {x y:Grade}{r d:ℕ}(hi:y∈items r d)(hj:x∈stairs r d y): leverage r d x< leverage r d y:= by
 have hy:= (belongs.mp hi).2; have hh:=mem_filter.mp hj; have hx:= (belongs.mp hh.1).2; unfold leverage;
 obtain he | ⟨hf,hf'⟩:= hh.2.2
 · have he' := Nat.mul_le_mul_right (d+3*r+1) he -- α x+1 ≤ y; Nat.lt reducible?
   rw [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at he'; omega
 rw [hf]; omega
lemma cost_le {r d x}(hi:x∈items r d): leverage r d x ≤ loft r d:= by
 unfold leverage loft; rw [Nat.add_mul,Nat.one_mul]; have hh:= Nat.mul_le_mul_right (d+3*r+1) (belongs.mp hi).1; omega

variable {X : Type} {U J : ℕ → Type}
variable (W:Scale X U)
/-- One weight regime for entire propagate statement. Independent of μ trajectory update,
 except nondecreasing as going finer (from operator control); includes polyadic and exponential
 lens realizations on all steps. -/
structure Rally {X : Type} {U:ℕ→Type} (W:Scale X U) where
 read : ∀ i,Lens (W.zoom i)
 onward (i:ℕ) : (read i).m ≤ (read (i+1)).m
namespace Rally
variable (O:Lens W.tape)
def native : Rally W := ⟨fun i=> W.localize i O, fun i=> W.kept i O (i+1) (Nat.le_succ _)⟩
variable (R:ℝ)
local notation "K" i => max (W.μ i) R
/-- Permit $\eta_i=min(\mu_i/R,1)$ when R positive, i.e. cap native distance weight in
 the fine region by (physical length)/R, potentially releasing approved Diamond boarding. -/
def hopped : Rally W where
 read i := {
      m := fun x=> O.m x / (max (W.μ i) R)
      sign := fun x=> div_nonneg (O.sign x) (le_trans (W.positive i).le (le_max_left ..))
      path := fun a b=> by
         change O.m a / (K i) ≤ O.m b / (K i) + (W.tape.Δ b a / W.μ i);
         have hy : 0≤ K i:= le_trans (W.positive i).le (le_max_left ..);
         apply le_trans (b:=(O.m b + W.tape.Δ b a) / (K i)) (div_le_div_of_nonneg_right (O.path ..) hy)
         rw [add_div]; exact add_le_add_right (div_le_div_of_nonneg_left (W.tape.sign ..) (W.positive i) (le_max_left ..)) _ }
 onward i x := div_le_div_of_nonneg_left (O.sign x) (lt_of_lt_of_le (W.positive (i+1)) (le_max_left ..)) (max_le_max (W.decreasing i) le_rfl)
end Rally
variable {W}
variable (F:Tier)(O:Rally W)
abbrev audible (i:ℕ) := (O.read i).m ∘ W.point i
def essence (i:ℕ) (P:Channel (U i))(x: Grade) := F.valueOf (audible O i) (cargo P x)
lemma essence_nn {i : ℕ} (P:Channel (U i))(x:Grade):0≤essence F O i P x := F.lower _ (fun k=>(O.read i).sign (W.point i k)) _

variable (V:Voyage U J) [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [∀ i,DecidableEq (U i)]
variable (G : ∀ i, Subring (Channel (U i)))
variable {γ R C :ℝ} {b N r d δ:ℕ}
local notation "L" => W.Y C R
local notation "φ" => W.fade γ

/-- h.Ward identity through order r at i+1 in one compatible gauge moving frame (left to
producer at the kernel origins on same functions). Before any splits by rank or visibility, with
alleles all choices simultaneous, no estimate on packet. All row budgets on $w'$ may use the
PRE-approved caps; no `stable` or periods supplied here. The pre cost on rank-diagonal may
budget only those positive ranks in certifiable input, e.g. rank≥2 with color scalar. All maps
and pre-constants can depend on i, scaling geometry fixed across working slab. -/
structure PassBook (V:Voyage U J) (W:Scale X U) (G: ∀ i,Subring (Channel (U i)))
    (F:Tier) (O:Rally W) (R C γ:ℝ) (δ b N r d:ℕ) : Prop extends Hours W R C δ b N where
  rich_gamma : 0 ≤ γ
  small : γ ≤ 1
  clock : (↑(loft r d):ℝ)≤ C^2
  powers : Voyage.authentic V G b N
  ranks : V.Eligible r b N
  stamp' : ∀ i∈Ico b N,∃ K : ℝ, ∃ w: U (i+1)→ Channel (U (i+1)⊕ U i),
       Inventory (orient (V.sail i) w) F (W.point (i+1)) (W.point i) (W.zoom i) (W.Y C R i ^ δ) r d ∧
       Pre (orient (V.sail i) w) ((O.read i).m ∘ W.point (i+1)) (audible O i) F K ∧
       ∀ P∈G (i+1),Guard P r d → (pass (V.sail i) w P r ∧
         ∀ x∈upstairs r d, cargo P x≠0 → (2*K)^x.2 ≤ W.fade γ (i+1) i)
variable {F O V G}
variable (h: PassBook V W G F O R C γ δ b N r d)

/-- Aging for each grade, changed after using availability estimate on present ranks. -/
def echo (W:Scale X U) (γ:ℝ)(x:Grade)(i:ℕ) := if 0<x.2 then W.fade γ (i+1) i else 1
local notation "ε" => echo W γ

omit [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] in
lemma echo_nn (x:Grade)(i:ℕ):0 ≤ ε x i:= by unfold echo; split_ifs <;> first | exact W.fade_nn | norm_num
include h
lemma echo_self (x:Grade)(i:ℕ): ε x i ≤ 1 := by unfold echo; split_ifs <;> first | exact W.fade_low h.rich_gamma (Nat.le_succ _) | rfl
variable {i : ℕ} {P:Channel (U (i+1))}
namespace PassBook
lemma words (hi:i∈Ico b N)(hp : P∈ G (i+1))(he:Guard P r d){x:Grade}(ht:x∈items r d): essence F O i ((V.sail i).floats P) x ≤ echo W γ x i * essence F O (i+1) P x + (L i)^(δ*expansive d r)* ∑ u∈stairs r d x, essence F O (i+1) P u := by
 obtain ⟨C₁,w,hv,hu,H⟩:= h.stamp' i hi; obtain ⟨hg,hf⟩:= H P hp he;
 let k := ((O.read i).m ∘ W.point (i+1)); let p u:= F.valueOf k (cargo P u); have hz : 0≤ k:=fun x=>(O.read i).sign (W.point (i+1) x); have hy u : 0≤ p u:= F.lower k hz _
 have h' u: p u≤ essence F O (i+1) P u:= by
    have he' : k ≤ audible O (i+1):= fun j=> O.onward i (W.point (i+1) j)
    have he := F.gain_under k _ hz (PowerSeries.C (cargo P u)) (k:=0) he'; simp_rw [Tier.gain_constant] at he; exact he
 have hx' : (2*C₁)^x.2 * p x ≤ ε x i * p x:= by
    by_cases hi': cargo P x=0
    · unfold p; rw [hi',Tier.zero]; simp
    unfold echo; split_ifs with hA; · exact mul_le_mul_of_nonneg_right (hf _ (mem_filter.mpr ⟨ht,hA⟩) hi') (hy x)
    rw [show x.2=0 by omega,pow_zero]
 rw [pow_mul]; apply le_trans (triangular w (O.read i) hv hu ht he hg); apply add_le_add (hx'.trans (mul_le_mul_of_nonneg_left (h' _) (echo_nn ..)))
 exact mul_le_mul_of_nonneg_left (sum_le_sum fun u _=> h' u) (pow_nonneg (pow_nonneg (h.toHours.paid (mem_Ico.mp hi).1) _) _)
end PassBook
end YM.FormalOPE.RG10.GaugeGear
