import YM.SchemeConversionRG11.FirstW.Kernel.Tide
/-! Compact-by-compact convergence price for normalized difference jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology
open scoped BigOperators
variable {T : Align.Itinerary} {K : Set E4} {A E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {f p : Board T E} {g : Board T F}
abbrev Sheets (E : Type*) := List Axis → E4→ E
def surface (D : List Axis) (f : Board T E) : Board T E := fun i=>((T.gap i)^D.length)⁻¹ • combine D (f i)
def ray (a : Axis) (f : Board T E) : Board T E := surface [a] f
def Score (T : Align.Itinerary) (K : Set E4) (f : Board T E) (W : Sheets E) := ∀ D, Meets T K (surface D f) (W D)
variable {W Y : Sheets E} {U : Sheets F}
lemma surface_root (f : Board T E) : surface [] f = f := by funext i x; simp [surface,combine]
lemma surface_add (D : List Axis) (f p : Board T E) : surface D (f+p) = surface D f + surface D p := by funext i; simp only [surface,Pi.add_apply,combine_add,smul_add]
lemma Score.identity (h : Score T K f W) : Meets T K f (W []) := by simpa only [surface_root] using h []
lemma Score.restrict {S : Set E4} (hk : K ⊆ S) (h : Score T S f W) : Score T K f W := fun D=>(h D).restrict hk
lemma Score.plus (h : Score T K f W) (e : Score T K p Y) : Score T K (f+p) (W+Y) := fun D=> by rw [surface_add]; exact (h D).plus (e D)
lemma Score.untouched : Score T K (0:Board T E) 0 := fun D=> by simpa only [show surface D (0:Board T E)=0 from funext (fun i=>by unfold surface; rw [Pi.zero_apply,combine_zero,smul_zero]),Pi.zero_apply] using (Meets.nil (T:=T) (S:=K) (E:=E)) -- simpa direction?
lemma Score.sum {f : A→Board T E} {W : A→Sheets E} (S : Finset A) (h : ∀ i∈S, Score T K (f i) (W i)) : Score T K (∑ i∈S,f i) (∑ i∈S,W i) := by
  classical
  induction S using Finset.induction with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Score.untouched
  | insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self _ _)).plus (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))
lemma Score.map (L : E→L[ℝ] F) (h : Score T K f W) : Score T K (fun i x=>L (f i x)) (fun D x=>L (W D x)) := by
  intro D
  have H := (h D).move L L.continuous
  exact H.congr (Eventually.of_forall fun i=> funext fun x=> by
    unfold surface
    have e:= congrFun (combine_map D L.toLinearMap.toAddMonoidHom (f i)) x
    rw [Pi.smul_apply,Pi.smul_apply,map_smul]; exact congrArg (fun y:F=> ((T.gap i)^D.length)⁻¹ • y) e.symm) (fun _ _=>rfl) -- EqOn binder implicit?
lemma Score.resite (h : Score T K f W) (o : StepPath T) {v : E4} (hz : sails T o v) (A : Set E4) (ha : ∀ x∈A,x+v∈K): Score T A (fun i x=>f i (x+o i)) (fun D x=> W D (x+v)) := fun D=>
  ((h D).quote o hz A ha).congr (Eventually.of_forall fun i=>funext fun x=>by simp only [surface, Pi.smul_apply,combine_shift]) (fun _ _=>rfl)
lemma Score.nudge (h : Score T K f W) (s : Cover) : Score T K (fun i x=>f i (x+wrap (T.period i) s)) W := fun D=>
 ((h D).east s).congr (Eventually.of_forall fun i=>funext fun x=>by simp only [surface, Pi.smul_apply,combine_shift]) (fun _ _=>rfl)
lemma surface_surface (D H : List Axis) (f : Board T E) : surface D (surface H f)=surface (D++H) f := by
  funext i; unfold surface; rw [combine_smul,append_op,smul_smul, List.length_append, pow_add, mul_inv]
lemma Score.insect (h : Score T K f W) (D : List Axis) : Score T K (surface D f) (fun H=> W (H++D)) := fun H=>by rw [surface_surface]; exact h _
def latest (B : E →L[ℝ] F→L[ℝ] G) : List Axis → Sheets E→Sheets F → E4→G
 | [],f,g,x=> B (f [] x) (g [] x)
 | i::D,f,g,x=> latest B D (fun H => f (H ++ [i])) g x + latest B D f (fun H=> g (H++[i])) x
-- recursion order changed, cost for combine i::D via D ⋅ i (on tail). discrete jet iterated commutes.
lemma surface_swap (D : List Axis) (i : Axis) (f : Board T E) : surface (i::D) f=surface (D++[i]) f := by funext j; unfold surface; rw [List.length_cons,List.length_append,append_op]; rw [combine]; exact congrArg (fun v => ((T.gap j)^(D.length+1))⁻¹ • v) (combine_up D i (f j)).symm
lemma ray_product (L : E →L[ℝ] F→L[ℝ] G) (f : Board T E) (g : Board T F) (j : Axis) :
    ray j (fun i x=>L (f i x) (g i x))=(fun (i:ℕ) (x : Site (T.period i))=>L (ray j f i x) (g i (x+step j))) + (fun (i:ℕ) (x:Site (T.period i))=>L (f i x) (ray j g i x)) := by
  funext i x; simp [ray, surface, combine, up, smul_sub]
lemma Score.product (L : E →L[ℝ] F→L[ℝ] G) (h : Score T K f W) (e : Score T K g U) : Score T K (fun i x=>L (f i x) (g i x)) (fun D=>latest L D W U) := by
  intro D; induction D generalizing f W g U with
  | nil=> rw [surface_root]; exact h.identity.price e.identity _ (show Continuous (uncurry fun x y=>L x y) from (L.continuous.comp continuous_fst).clm_apply continuous_snd)
  | cons i D ih =>
    rw [surface_swap,←surface_surface]; change Meets _ _ (surface D (ray i _)) _; rw [ray_product, surface_add]
    have he : Score T K (fun j x=>g j (x+step i)) U := by simpa only [wrap_step] using e.nudge (step i)
    exact (ih (h.insect [i]) he).plus (ih h (e.insect [i]))
lemma Score.origin : Score T {x:E4 | x≠0} (E:=ℝ) (fun i=> (T.gap i ^2)⁻¹ • linGreen (T.period i)) (fun D x=>(Band.casual D x).re) := by
  intro D σ hs v hv o ho
  have H := tor_limit (Rig.path T σ hs) D hv o ho
  apply H.congr; intro i; unfold surface; rw [combine_smul,smul_smul,pow_add, mul_inv]
  rfl
end YM.RG11.FirstW
