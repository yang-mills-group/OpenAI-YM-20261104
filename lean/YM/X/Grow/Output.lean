import YM.X.Grow.Kite
/-!
# Real brush Taylor currents and their grading. Open dynamical CT use only local real slots even on global-color orbits. No estimates here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open MvPolynomial Function Lattice Next.Rank Normal LiftMark Maxwell Maxwell.Free Finset Reed Stems
open scoped Topology Classical Pointwise
variable {G:Gauge} {V W I:Type*} {u:V→ℕ}{n m k:ℕ}
section
variable (E:ℕ→Type*) [∀ n, AddCommGroup (E n)][∀ n,Module ℝ (E n)][∀ n,FiniteDimensional ℝ (E n)]
variable (Y:(n:ℕ)→ E n →ₗ[ℝ] Brush G)
local notation "F"=> poly (Kite E)
def towerP (n:ℕ)(i:Fan G):F:=colorL n (E:=E) (taste i ∘ₗ (Y n))
def bunch (n:ℕ)(i:Fan G):F:= ∑ j∈range n,towerP E Y j i
lemma pillar {i:Fan G}(x:(n:ℕ)→E n)(n:ℕ) (h: Y n= Y n:=rfl): probeL x (towerP E Y n i)=(taste i (Y n (x n)) :ℂ):= eyes ..
lemma bunched {i:Fan G}(x:(n:ℕ)→E n)(n:ℕ): probeL x (bunch E Y n i)= (taste i (∑ j∈range n,Y j (x j)):ℂ):= by unfold bunch; simp_rw [map_sum,pillar E Y x _ rfl,Complex.ofReal_sum]

def trumpet (n:ℕ): Curly G→ₐ[ℂ] F := MvPolynomial.aeval (fun i:Hair G=> bunch E Y n (Finsupp.single i 1))
def shorn (n:ℕ): Curly G→ₗ[ℂ] F := (LiftMark.level (gear E) n) ∘ₗ (trumpet E Y n).toLinearMap
lemma tone (n:ℕ)(p:Curly G) (x:(n:ℕ)→E n): probeL x (trumpet E Y n p)= snap (∑ i∈range n,Y i (x i)) p:= by
    apply DFunLike.congr_fun (f:=(probeL x).comp (trumpet E Y n)); ext1 j; rw [AlgHom.comp_apply,trumpet,MvPolynomial.aeval_X,bunched,taste_eval,flat₁]; simp [Stems.snap]
lemma tru (n:ℕ)(i:Fan G): trumpet E Y n (glyph (com i))=bunch E Y n i:= by
    apply probe_ext; intro x; rw [tone,bunched,com_text,snaps_blade,taste_eval];rfl
lemma few (h:n≤k)(p:Curly G): level (gear E) n (trumpet E Y k p)= shorn E Y n p:= by
    refine LiftMark.verdict_map («F»:=trumpet E Y k) (Q:=trumpet E Y n) n (gear E) ?cond p
    case cond =>
       intro i; repeat rw [trumpet, MvPolynomial.aeval_X]
       let t(j:ℕ):= towerP E Y j (Finsupp.single i 1); change level (gear E) n (∑ j∈range k,t j)=level (gear E) n (∑ j∈range n,t j); rw [map_sum,map_sum]; symm; refine sum_subset (range_mono h) ?_; intro j _ hj
       have h : n<j+1:=by simp_all only [mem_range]; omega
       exact (Strong.of_pure (gears (E:=E) j (taste (Finsupp.single i 1) ∘ₗ Y j))).none h
lemma few_commute (h:n≤k)(p:Curly G): level (gear E) n (shorn E Y k p)=shorn E Y n p:= by
    rw [← few E Y h p]; let z:= trumpet E Y k p; ext i; change coeff i (Rise.trim (Rise.trim z (gear E) k) _ n)=coeff i (Rise.trim z _ n); simp only [Rise.trim_coeff]; split_ifs <;> first|rfl|omega -- parser

end

abbrev Valves(G:Gauge):= Kite (Okay G)
abbrev vapor (G:Gauge):= gear (Okay G)
abbrev Book (G:Gauge):= poly (Valves G)
local notation "v"=> vapor G
abbrev bloom (n:ℕ): Curly G→ₗ[ℂ] Book G:= shorn (Okay G) valP n
lemma bloomed {i:Fan G} (h:i∈grads G m)(j:ℕ)(hj:j<m): towerP (Okay G) valP j i=0:= by
    apply probe_ext; intro x; rw [pillar _ _ x j rfl,taste_eval,lif, launch,vanish_step i h _ hj]; simp
lemma owngear (k:ℕ)(z:Fan G):IsWeightedHomogeneous (vapor G) (towerP (Okay G) valP k z) (k+1):= by
    have h:= gears (E:=Okay G) k ((taste z).comp (valP (G:=G) k)); exact h
lemma bulges {i:Fan G}(h:i∈grads G m) (n:ℕ): Strong (vapor G) (m+1) (bunch (Okay G) valP n i) := by
    unfold bunch; apply Strong.sum (range n); intro j hj; by_cases hp:j < m; · rw [bloomed h _ hp]; exact Strong.zero
    exact (Strong.of_pure (owngear j i)).weaken (by omega)
lemma lite {i:Fan G}(h:i∈grads G m) (j:ℕ)(hj:m<j): level (vapor G) (m+1) (trumpet (Okay G) valP j (glyph (com i)))= towerP (Okay G) valP m i:= by
    rw [tru,bunch,map_sum, sum_eq_single_of_mem m (mem_range.mpr hj),trimmer_hom (le_refl (m+1)) (owngear m i)]; intro j _ hnot
    rcases lt_or_gt_of_ne hnot with hp|hp
    · rw [bloomed h j hp,map_zero]
    exact (Strong.of_pure (owngear j i)).none (by omega)
end YM.PositionX.Grow
