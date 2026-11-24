import YM.OPE.Loom.Levels
import YM.OPE.Loom.Gate
/-!
# Cut threshold for the single root assembly
At finer levels pay `Repegs`; at coarser ones stop. Using only constant strength e.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
variable {G:Gauge} {C:Family G} {I : Type*} {φ : Filter I} {T a c : I→ℝ} {m k : I→ℕ} {b v : ℝ}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "P" => C.path.levels.budget
set_option quotPrecheck false
-- can enlarge multiplier for tighter radius recharge at events

def count (C:Family G)(f i:ℕ) := Nat.ceil ((f:ℝ)*Real.log (C.path.levels.clock.hatBeta (i+1)))
def stride (C:Family G)(f i:ℕ) := (C.path.levels.budget i).B*(count C f i+2)+4
def threshold (C:Family G)(f i:ℕ) := stride C f i*C.S.a i
lemma count_pos {f i : ℕ}(hf:0<f) : 0<count C f i:=Nat.ceil_pos.mpr (mul_pos (by positivity) (Real.log_pos ((Y).fits.delayed _)))
lemma count_le {f i : ℕ} : (count C f i:ℝ) ≤ (f:ℝ)*Real.log (X (i+1))+1 := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg (α:=ℝ) _) (Real.log_nonneg ((Y).fits.delayed _|>.le)))).le
lemma count_cost (hT:Tendsto T φ atTop)(h:Height C.S φ T m b)(f:ℕ) : Cheap φ T (fun i=>(count C f (m i):ℝ)):=by
   have he:= (hat_price hT (h.step (Y).fits.mesh)).up; have hh : Cheap φ T (fun i=> f*(X (m i+1))+1):= Bill.add (Cheap.mul (Bill.const (f:ℝ) hT) he) (Bill.const 1 hT) hT
   refine hh.norm_le (Eventually.of_forall ?_); intro i; let k:=m i; have hp:0<X (k+1):= zero_lt_one.trans ((Y).fits.delayed _)
   rw [Real.norm_of_nonneg (by positivity)]; apply le_trans _ (Real.le_norm_self _); refine count_le.trans ?_; gcongr; exact Real.log_le_self hp.le
lemma stride_cost (hT:Tendsto T φ atTop)(h:Height C.S φ T m b)(f:ℕ) : Coins φ T (fun i=>(stride C f (m i):ℝ)):= by
   apply Coins.by_le; · unfold stride; push_cast; exact Bill.add (Cheap.mul (covers_p hT h|>.up) ((count_cost hT h f).add (Bill.const (2:ℝ) hT) hT)) (Bill.const 4 hT) hT
   filter_upwards with i; apply le_trans _ (Real.le_norm_self _); exact_mod_cast (show 1 ≤ stride C f (m i) by unfold stride;omega)
lemma gate_b (f k:ℕ) : (S).a k ≤ threshold C f k:= le_mul_of_one_le_left ((S).a_pos k|>.le) (Nat.one_le_cast.mpr (by unfold stride; omega))
lemma threshold_cost (hT:Tendsto T φ atTop)(h:Height C.S φ T m b)(f:ℕ) : Bi φ T (fun i=>threshold C f (m i)) (fun i=>(S).a (m i)):= by
   unfold threshold; simpa using! Bi.mul (stride_cost hT h f) (Bi.refl φ T (C.S.a ∘ m))
lemma threshold_rate (hT:Tendsto T φ atTop)(h:Height C.S φ T m b)(f:ℕ) : RateIs φ T (fun i=>threshold C f (m i)) (-b) := known hT (threshold_cost hT h _) h.mesh (Eventually.of_forall fun _=> (C.S.a_pos _).trans_le (gate_b ..))
variable (K:ℕ)
lemma peak (C:Family G) : Tendsto (threshold C K) atTop (𝓝 0):= (threshold_rate (C:=C) C.S.divergent first_price K).tends (by norm_num) C.S.divergent
section
open scoped Classical
private def lag (C:Family G) (s:ℝ) : Finset ℕ := if h:0<s then Set.Finite.toFinset (s:={j| s ≤ threshold C K j}) (by
   obtain ⟨j,hj⟩:= eventually_atTop.mp ((peak K C).eventually (gt_mem_nhds h)); exact (Set.finite_lt_nat j).subset (fun i hi=> lt_of_not_ge (fun hk=> not_lt_of_ge hi (hj i hk)))) else ∅
-- max(0, last failed length)
def arch (C:Family G) (s:ℝ) : ℕ := (lag K C s).sup id
private lemma ranks {i:ℕ} (hp:0<v) : i ∈ lag K C v ↔ v ≤ threshold C K i:= by unfold lag; rw [dif_pos hp]; exact Set.Finite.mem_toFinset _
lemma beyond {i:ℕ} (hp:0<v)(h:v ≤ threshold C K i) : i ≤ arch K C v:= Finset.le_sup (f:=id) ((ranks K hp).2 h)
lemma before {i:ℕ}(hp:0<v)(h: arch K C v < i) : threshold C K i < v:= lt_of_not_ge (fun he=>h.not_ge (beyond K hp he))
lemma arch_fails {i:ℕ}(hp:0<v)(h:v ≤ threshold C K i) : v ≤ threshold C K (arch K C v):=by obtain ⟨j,hj,he⟩:= Finset.exists_mem_eq_sup _ (show (lag K C v).Nonempty from ⟨_,(ranks K hp).2 h⟩) id; change arch K C v=j at he; rw [he]; exact (ranks K hp).1 hj
lemma arch_mono {w:ℝ}(hp:0<v)(h:v ≤ w): arch K C w ≤ arch K C v:= by
   apply Finset.sup_mono; intro i hi; exact (ranks K hp).2 (h.trans ((ranks K (hp.trans_le h)).1 hi)) -- explicit f?
lemma arch_growth (C:Family G) (h:Tendsto a φ (𝓝[>]0)) : Tendsto (fun i=>arch K C (a i)) φ atTop:=tendsto_atTop.mpr fun j=> by filter_upwards [h.eventually (Ioc_mem_nhdsGT ((C.S.a_pos j).trans_le (gate_b K j)))] with i hi using beyond K hi.1 hi.2
end
end YM.OPE.Loom
