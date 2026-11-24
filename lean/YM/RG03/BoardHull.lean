import YM.RG03.BoardDepth

/-!
# A possible short *common* hull for all exchange corrections

Balls in the actual torus containing all vertices and touched plaquette bases. Flags still need
`UsesFinal.allReads` (including `inspected`) when pushing an interaction through a finer
integration. On the present torus the derivative and support-exponent charges use the actual
`coverNumber`; this short-hull result can apply only when the base radius or another larger cover
estimate pays for the enlargement, not to suppress a winding by declaring it short.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Tight
open RG Wilson Lattice PathWords Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}

private lemma step_dist (z:Site n)(a:Step) : separation z (z+a.vec) ≤ 1 := by
  rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _
lemma on_walk (z:Site n)(w:Walk) : ∀ x∈visits z w,separation z x ≤ w.length := by
  induction w generalizing z with
  | nil => intro x hx; rw [show x=z from by simpa [visits] using hx,separation_self]; exact Nat.zero_le _
  | cons a w ih =>
    intro x hx; simp only [List.length_cons]
    rcases List.mem_cons.mp hx with hx|hx
    · rw [hx,separation_self]; simp
    refine (separation_triangle z (z+a.vec) x).trans (by have := ih (z+a.vec) x hx; have := step_dist z a; omega)
private lemma stop_visit (z:Site n)(w:Walk): stop z w∈visits z w := by induction w generalizing z <;> simp_all [visits,stop]

def cage (l:ℕ) (o:Site n) := halo (2*l+4) {o}
lemma at_cage {l:ℕ}{o x:Site n} : x∈cage l o ↔ separation o x ≤ 2*l+4 := halo_spec.trans (by simp)
lemma cage_subset {l L:ℕ} (he:l≤L) (o:Site n) : cage l o ⊆ cage L o := by
  intro i hi; rw [at_cage] at hi ⊢; omega
lemma in_cage {l:ℕ}{c:Circuit}(hr:c.prefix'.length ≤ l)(o:Site n) : c.supply o (cage l o) := by
  have ht := on_walk o c.prefix' _ (stop_visit o c.prefix')
  have he (x:Site n) (a:Step) : separation x (x+ (if a.neg then a.vec else 0)) ≤ 1 := by
    split
    · apply step_dist
    simp
  have he' := separation_triangle o (c.start o) (c.start o+ (if c.a.neg then c.a.vec else 0))
  have hp (a b:Step) : separation (c.start o+(if a.neg then a.vec else 0)) (atFace (c.start o) a b) ≤ 1 := by
    exact he (c.start o+if a.neg then a.vec else 0) b
  have hq := separation_triangle o (c.start o+(if c.a.neg then c.a.vec else 0)) (atFace (c.start o) c.a c.b) -- hq already argument?
  refine Or.inr (at_cage.mpr ?_)
  have hs : Circuit.start c o = stop o c.prefix' := rfl
  change _ ≤ _
  have hf := hp c.a c.b
  have hg := he (c.start o) c.a
  change separation o (atFace _ _ _) ≤ _
  rw [← hs] at ht; omega

lemma word_local {l:ℕ}{w:Word}(hr:short w l)(o:Site n) : LocalOn (cage l o) (value (G:=G) w o) := by
  intro U V huv
  suffices e : ∀ i∈w, i.defect o U=i.defect o V by apply congr_arg List.prod; exact List.map_congr_left e
  intro c hc; unfold Circuit.defect Circuit.raw;congr 2
  apply Circuit.holonomy_local ..
  apply agrees_mono huv; intro x hx
  rw [mem_coe,List.mem_toFinset] at hx
  have he:=on_walk o c.path x hx; have hs := hr c hc
  have hl : c.path.length=2*c.prefix'.length+4 := by unfold Circuit.path oriented Lattice.reverse; simp; omega
  exact at_cage.mpr (by omega)

lemma word_gauge (w:Word) (o:Site n)(u:Site n→G.El)(U:Config G n) :
    value w o (gauge u U) = G.mat (u o) * value w o U * G.mat (u o)⁻¹ := by
  have hh : G.mat (u o)* G.mat (u o)⁻¹ = 1 := by rw [← G.mat_mul]; simp
  have hi : G.mat (u o)⁻¹*G.mat (u o)=1 := by rw [← G.mat_mul]; simp
  have he (c:Circuit) : c.defect o (gauge u U) = G.mat (u o)*(c.defect o U)*G.mat (u o)⁻¹ := by
    simp_rw [Circuit.defect,Circuit.raw,Circuit.conjugation,G.mat_mul]
    calc _ = G.mat (u o) * G.mat (c.holonomy o U) * G.mat (u o)⁻¹ - G.mat (u o)*G.mat (u o)⁻¹ := by rw [hh]
         _ = _ := by noncomm_ring
  induction w with
  | nil => simpa only [value_nil,mul_one] using hh.symm
  | cons c w ih => rw [value_cons,value_cons,he,ih]; simp only [mul_assoc,show ∀x:G.Mat, G.mat (u o)⁻¹*(G.mat (u o)*x)=x from fun x=>by rw [← mul_assoc,hi,one_mul]]

open Boards
variable {E:Type*} [AddCommMonoid E][Module ℝ E]{ι:Type*}

def Together (T:Token G E ι) : Prop := ∀ u z, T (fun i=> G.mat u * z i * G.mat (u⁻¹))=T z

lemma price_local (T:Token G E ι) {r:Board ι}{l:ℕ}(hr:radius r l)(o:Site n): LocalOn (cage l o) (price T r o) := by
  intro U V H; apply congr_arg T; exact funext (fun i=> word_local (hr i) o U V H)
lemma price_invariant {T:Token G E ι} (h:Together T)(r:Board ι)(o:Site n): GaugeInvariant (price T r o) := by
  intro u U
  exact (congr_arg T (funext fun i=>word_gauge (r i) o u U)).trans (h (u o) (arrayValue r o U))
end YM.RG03.Tight
