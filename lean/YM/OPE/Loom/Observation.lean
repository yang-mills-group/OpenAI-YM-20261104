import YM.OPE.Loom.Scales
/-!
# Observation mesh one step finer than last failed budget envelope
All finite positions eventually taken on a comparison grid inside a polynomial of T,
with the span and interpolation constants disclosed. Keep tabs for overshoot.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
variable {G:Gauge} {C:Family G} {I : Type*} {φ : Filter I} {T a : I→ℝ} {k : I→ℕ} {b v η: ℝ}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "P" => C.path.levels.budget
set_option quotPrecheck false
-- observations beyond both gates at all finer absorption & budgeted

def broad (C:Family G)(K k:ℕ) := threshold C K k *(((C.path.levels.budget k).B:ℝ)^2+1)
variable (K:ℕ)
lemma broad_fits (C:Family G)(k:ℕ): threshold C K k ≤ broad C K k:= le_mul_of_one_le_right (((C.S.a_pos _).trans_le (gate_b K k)).le) (le_add_of_nonneg_left (sq_nonneg (_:ℝ)))
lemma broad_price (hT:Tendsto T φ atTop)(h:Height C.S φ T k b) : Bi φ T (fun i=>broad C K (k i)) ((S).a ∘ k) := by
   refine ⟨?_ ,(threshold_cost hT h K).down.mono ?_⟩
   · simpa only [broad,mul_one] using! Bill.mul (threshold_cost hT h K).up ((Cheap.power (covers_p hT h|>.up) hT 2).add (Bill.const (1:ℝ) hT) hT)
   apply Eventually.of_forall; intro i; rw [Real.norm_of_nonneg (( (C.S.a_pos _).trans_le (gate_b K (k i))).le)]; exact (broad_fits K C _).trans (Real.le_norm_self _)
private lemma broad_pays (C:Family G) : RateIs atTop C.S.scale (broad C K) (-1):= known C.S.divergent (broad_price K C.S.divergent first_price) first_price.mesh (Eventually.of_forall (fun i=> (C.S.a_pos _).trans_le ((gate_b K _).trans (broad_fits K C i))))
-- choose maximal level once, price accounts for step. No interpolation inside the parameter.
private def select (C:Family G) (v:ℝ) : Finset ℕ := if h:0<v then Set.Finite.toFinset (s:={j| v ≤ broad C K j}) (by
   obtain ⟨j,hj⟩:= eventually_atTop.mp ((broad_pays K C|>.tends (by norm_num) C.S.divergent).eventually (gt_mem_nhds h)); exact (Set.finite_lt_nat j).subset (fun i hi=> lt_of_not_ge (fun hk=> not_lt_of_ge hi (hj i hk)))) else ∅
def observ (C:Family G)(v:ℝ) : ℕ:= (select K C v).sup id +1
private lemma select_eq {i:ℕ} (hp:0<v) : i ∈ select K C v ↔ v ≤ broad C K i:= by unfold select; rw [dif_pos hp]; exact Set.Finite.mem_toFinset _
lemma fine_all {i:ℕ}(hp:0<v)(hv:v ≤ broad C K i): i < observ K C v:= Nat.lt_succ_of_le (Finset.le_sup (f:=id) ((select_eq K hp).2 hv))
lemma fine_value (hp:0<v): broad C K (observ K C v) < v:= lt_of_not_ge (fun hv=> lt_irrefl _ (fine_all K hp hv))
lemma fine_prior (hp:0<v)(hv:v ≤ broad C K 0): v ≤ broad C K (observ K C v-1):= by obtain ⟨j,hj,he⟩:= Finset.exists_mem_eq_sup _ (show (select K C v).Nonempty from ⟨_,(select_eq K hp).2 hv⟩) id; rw [observ, Nat.add_sub_cancel, he]; exact (select_eq K hp).1 hj
lemma focus (C:Family G) (ha:Tendsto a φ (𝓝[>]0)) : Tendsto (fun i=>observ K C (a i)) φ atTop:= tendsto_atTop.mpr fun k=>by filter_upwards [ha.eventually (Ioc_mem_nhdsGT ((C.S.a_pos _).trans_le ((gate_b K k).trans (broad_fits ..))))] with i hi using (fine_all K hi.1 hi.2).le
lemma ordinary (C:Family G)(h:Tendsto a φ (𝓝[>]0))(hT:Tendsto T φ atTop)(ha:RateIs φ T a (-b))(H:Stock.Tabs C.path.levels) : let k i:= observ K C (a i)
          Height C.S φ T k b ∧ Bi φ T (fun i=>C.S.a (k i)) a :=by
   intro k; let m i:=k i-1; have hu:Tendsto k φ atTop:= focus _ _ h
   let c:=C.S.a; let d j:= broad C K (j-1); have hx : RateIs atTop C.S.scale d (-1):= known C.S.divergent ((broad_price K C.S.divergent (prec (C:=C) first_price)).trans (shift_back C.S.divergent first_price H)) first_price.mesh (Eventually.of_forall fun i=> ((C.S.a_pos _).trans_le ((gate_b K _).trans (broad_fits K C _))))
   have hb : ∀ᶠ i in φ,a i ≤ broad C K (m i):= ((h.eventually (Ioc_mem_nhdsGT ((C.S.a_pos _).trans_le ((gate_b K 0).trans (broad_fits K C _)))))).mono fun i hi=> fine_prior K hi.1 hi.2
   have hv : ∀ᶠ i in φ,c (k i)≤ a i := ha.pos.mono fun i hi=> (gate_b K (k i)).trans ((broad_fits K C _).trans (fine_value K hi).le)
   have ht:= straddles C hu c d hT first_price.mesh hx ha (hv.and hb)
   have he := ((broad_price K hT (prec ht)).trans (shift_back hT ht H)).up
   refine ⟨ht,Bill.made (hv.mono fun i hi=> (Real.norm_of_nonneg ((C.S.a_pos _)|>.le)).trans_le (hi.trans (Real.le_norm_self _))),he.norm_le ((ha.pos.and hb).mono fun i ⟨hi,h⟩=> ?_)⟩
   exact (Real.norm_of_nonneg hi.le).trans_le (h.trans (Real.le_norm_self _))
end YM.OPE.Loom
