import YM.SchemeConversionRG11.FirstW.Kernel.Circ
import YM.Pert.Rig.Linked
/-! Moving limits on an orbit-centered stencil around any reporting mark.
For FirstW use simply fixed separated positions incl along all subsequences. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Set Metric Filter Lattice Pert Pert.Align Topology
open scoped Topology ContDiff BigOperators
variable {E F G X : Type*}
local notation "M" => Align.Itinerary
def out (T : M) (i) (x : Site (T.period i)) : E4 := Full.incVec (T.gap i) (lift x)
def sails (T : M) (f : ∀ i:ℕ,Site (T.period i)) (v : E4) := Tendsto (fun i=> out T i (f i)) atTop (𝓝 v)
variable {S K A : Set E4} {T : M} {σ : ℕ→ℕ}
lemma seals {u : ℕ→Cover} {v : E4} (hu : Tendsto (fun i=>Full.incVec (T.gap i) (u i)) atTop (𝓝 v)) : ∀ᶠ i in atTop,Lattice.lift (wrap (T.period i) (u i))=u i := (simple_bounds T hu).mono fun i hi=> lift_eq_iff.mpr ⟨rfl,fun k=>by have:=hi k; have hh:=neg_le_abs (u i k); have hl:=le_abs_self (u i k); omega⟩
lemma sails_wrap {u : ℕ→Cover} {v : E4} (hu : Tendsto (fun i=>Full.incVec (T.gap i) (u i)) atTop (𝓝 v)) : sails T (fun i=>wrap (T.period i) (u i)) v := by
  unfold sails out; apply hu.congr'; filter_upwards [seals hu] with i hi; rw [hi]
variable {f g : ∀ i:ℕ,Site (T.period i)} {v w : E4}
lemma sails_add (hf : sails T f v) (hg : sails T g w) : sails T (f+g) (v+w) := by
  have hv : Tendsto (fun i=>Full.incVec (T.gap i) (lift (f i)+lift (g i))) atTop (𝓝 (v+w)) := by simp_rw [inc_add]; exact Tendsto.add hf hg
  simpa [← Pi.add_def] using sails_wrap hv
lemma sails_neg (hf : sails T f v) : sails T (-f) (-v) := by
  have he (i : ℕ) : Full.incVec (T.gap i) (-(lift (f i)))=-out T i (f i) := by ext; simp [out]
  have hv : Tendsto (fun i=>Full.incVec (T.gap i) (-lift (f i))) atTop (𝓝 (-v)) := by simp_rw [he]; exact Tendsto.neg hf
  simpa [← Pi.neg_def] using sails_wrap hv
lemma sails_sub (hf : sails T f v) (hg : sails T g w) : sails T (f-g) (v-w) := by rw [sub_eq_add_neg,sub_eq_add_neg]; exact sails_add hf (sails_neg hg)
lemma sails_step (z : Cover) : sails T (fun i=>wrap (T.period i) z) 0 := sails_wrap (T:=T) (inc_const T z)
lemma sails_next (hf : sails T f v) (z : Cover) : sails T (fun i=> f i+wrap (T.period i) z) v := add_zero v ▸ sails_add hf (sails_step z)
lemma sails_more (hs : Tendsto σ atTop atTop) (hf : sails T f v) : sails (Rig.path T σ hs) (fun i=>f (σ i)) v := by
  unfold sails at *
  exact hf.comp hs
abbrev Board (T : M) (E : Type*) := ∀ i:ℕ, Site (T.period i) → E
section movement
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
variable {f : Board T E} {g : Board T F} {W : E4→E} {Z : E4→F}
def Meets (T : M) (S : Set E4) (f : Board T E) (W : E4→E) := ∀ (σ : ℕ→ℕ) (hs : Tendsto σ atTop atTop) (v) (_:v∈S) (o : ∀ i, Site (T.period (σ i))), sails (Rig.path T σ hs) o v → Tendsto (fun i=> f (σ i) (o i)) atTop (𝓝 (W v))
lemma Meets.restrict (h : Meets T S f W) (hS : K ⊆ S) : Meets T K f W := fun σ hs w hw=>h σ hs w (hS hw)
lemma Meets.congr (h : Meets T S f W) {f' : Board T E}{W' : E4→E} (e : ∀ᶠ i in atTop, f i=f' i) (z : EqOn W W' S) : Meets T S f' W' := by
  intro σ hs v hv o ho; rw [← z hv]; exact (h σ hs v hv o ho).congr' ((hs.eventually e).mono fun i hi=>congrFun hi (o i))
lemma Meets.move (h : Meets T S f W) (L : E→F) (hl : Continuous L) : Meets T S (fun i p=>L (f i p)) (L ∘ W) := fun σ hs v hv o ho=> hl.continuousAt.tendsto.comp (h σ hs v hv o ho)
lemma Meets.price (h : Meets T S f W) (p : Meets T S g Z) (L : E→F→G) (hl : Continuous (uncurry L)) : Meets T S (fun i x=>L (f i x) (g i x)) (fun v=>L (W v) (Z v)) := fun σ hs v hv o ho => hl.continuousAt.tendsto.comp ((h σ hs v hv o ho).prodMk_nhds (p σ hs v hv o ho))
lemma Meets.quote (h : Meets T S f W) (p : ∀ i, Site (T.period i)) (hz : sails T p v) (K : Set E4) (H : ∀ x∈K,x+v∈S) : Meets T K (fun i x=> f i (x+p i)) (fun x=>W (x+v)) := fun σ hs _ hx _ ho=> h σ hs _ (H _ hx) _ (sails_add ho (sails_more hs hz))
lemma Meets.east (h : Meets T S f W) (p : Cover) : Meets T S (fun i x=>f i (x+wrap (T.period i) p)) W := fun σ hs _ hv _ ho=> h σ hs _ hv _ (sails_next ho p)
end movement
section expense
variable [NormedAddCommGroup E] {f g : Board T E} {W Z : E4 → E}
lemma Meets.rent (h : Meets T S f W) (hc : IsCompact K) (hq : K ⊆ S) : ∃ C : ℝ,0 < C ∧ ∀ᶠ i in atTop,∀ x : Site (T.period i), out T i x∈K → ‖f i x‖ ≤ C := by
  by_contra! he
  have hv (i : ℕ) : ∃ n≥i,∃ x : Site (T.period n), out T n x∈K ∧ (i:ℝ)+1 < ‖f n x‖ := frequently_atTop.1 (he ((i:ℝ)+1) (by positivity)) _
  choose n hn x hx hy using hv
  obtain ⟨z,hz,σ,hs,Hs⟩ := hc.isSeqCompact (x:=fun i=>out T (n i) (x i)) hx
  let b:= hs.tendsto_atTop
  let c := (tendsto_atTop_mono (f:=id) hn tendsto_id).comp b
  have hd := (h (n ∘ σ) c z (hq hz) (fun i=>x (σ i)) Hs).norm
  obtain ⟨i,hi,hj⟩ := (hd.eventually (gt_mem_nhds (lt_add_one ‖W z‖)) |>.and ((tendsto_natCast_atTop_atTop.comp b).eventually (eventually_ge_atTop ‖W z‖))).exists
  exact not_lt.mpr (show (σ i:ℝ)+1 ≥ ‖f (n (σ i)) (x (σ i))‖ from hi.le.trans (add_le_add hj le_rfl)) (hy (σ i))
lemma Meets.plus (h : Meets T S f W) (e : Meets T S g Z) : Meets T S (f+g) (W+Z) := fun σ hs v hv o ho=> (h σ hs v hv o ho).add (e σ hs v hv o ho)
lemma Meets.diff (h : Meets T S f W) (e : Meets T S g Z) : Meets T S (f-g) (W-Z) := fun σ hs v hv o ho=> (h σ hs v hv o ho).sub (e σ hs v hv o ho)
lemma Meets.nil : Meets T S (0:Board T E) 0 := fun _ _ _ _ _ _ => tendsto_const_nhds
lemma Meets.sum {f : X→Board T E} {W : X→E4→E} (A : Finset X) (h : ∀ i∈A, Meets T S (f i) (W i)) : Meets T S (∑ i∈A,f i) (∑ i∈A,W i) := by
  classical
  induction A using Finset.induction with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Meets.nil
  | insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self _ _)).plus (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))
end expense
end YM.RG11.FirstW
