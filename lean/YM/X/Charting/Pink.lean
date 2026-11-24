import YM.X.Charting.Apart
/-!
Compensation at weight inverse propagator for cross lines. Exact for off-shell cubic members. Abstract form.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "X'"=> MvPolynomial.X
variable {α β V:Type*}
local notation "iS"=> α⊕V
variable (P:poly α)(S:poly V)(Q : Symmetric (α⊕V))

def widen (w:ℂ) (a:iS): iS→₀ ℂ:= Finsupp.single a (Sum.elim (fun _=>1) (fun _=> w) a)
def wide (w:ℂ)(Q:Symmetric iS):= scope (widen w) (noHome Q)
lemma widen_l (w:ℂ): exchange (widen w) ((co (V:=V)) P) = co P := by
    apply DFunLike.congr_fun (f:=(exchange (widen w)).comp co); ext i; simp [widen,co]
lemma widen_gain (w:ℂ){p:Curly G}(hp:p∈ tripleSpan G): exchange (widen (α:=α) w) (coda p) =w^3 • coda p:= by
   let C:=coda (α:=α) (V:=Hair G); let R:= exchange (V:=α⊕Hair G) (widen w); apply sub_eq_zero.mp; change p∈ LinearMap.ker (R.toLinearMap.comp C.toLinearMap-w^3 • C.toLinearMap); apply Submodule.span_le.mpr ?_ hp; rintro x ⟨a,b,c,h,h',hy,rfl⟩; change R (C (X' a*(X' b*X' c))) - w^3 • (C (X' a*(X' b*X' c)))=0; apply sub_eq_zero.mpr; unfold R C coda; simp only [map_mul,rename_X,exchange_x,widen,Normal.glyph,linearCombination_single]; change _= _; dsimp only [Sum.elim]; rw [← C_mul', ← C_mul', ← C_mul', ← C_mul',map_pow]; ring
lemma cush (w:ℂ) {p:Curly G}(hp:p∈tripleSpan G){Q:Symmetric (α⊕ Hair G)}(H:∀ i j:Hair G,i.2≠ j.2→ Q.cov (.inr i) (.inr j)=0): w^3 * shock Q (co P*coda p)=shock (wide w Q) (co P*coda p):= by
   have ht : shock (noHome Q) (exchange (widen w) (co P*coda p))= shock (wide w Q) (co P*coda p) := by
       unfold shock; rw [wets,show reads (widen w) (0:α⊕Hair G→ℂ)= 0 from funext fun i=>by simp [reads,widen]]; rfl
   rw [←ht,map_mul (f:=exchange (widen w)) (co (V:=Hair G) P) (coda p), widen_l, widen_gain w hp, mul_smul_comm, map_smul, result, freezes _ _ hp]; rfl
   intro i j; rw [peel,remap_cov]; apply H

variable (M:ℕ→Symmetric (α⊕Hair G))(w:ℕ→ℂ)
lemma windy (h:∀ i j:α,Ripe q (fun k=>(M k).cov (.inl i) (.inl j)) 0)(g:∀ (i:Hair G)(j:α),Ripe q (fun k=>w k*(M k).cov (.inr i) (.inl j)) 0): ∀ i j:α⊕Hair G, Ripe q (fun k=>(wide (w k) (M k)).cov i j) 0:= by
   have he (s j): Ripe q (fun k=>(wide (w k) (M k)).cov (.inr s) (.inl j)) 0:= by
       refine (g s j).congr_left (fun i=> ?_); simp only [wide,scope,widen,treats,linearCombination_single,Sum.elim_inl,Sum.elim_inr,one_smul,Pi.smul_apply]; rw [Normal.Symmetric.symm (noHome ..),peel_l, (M i).symm]; rfl
   rintro (i|i) (j|j)
   · simp_rw [wide,scope,widen,treats,linearCombination_single, Sum.elim_inl,one_smul,peel_l]; exact h i j
   · convert he j i using 1; ext1 k; exact (wide _ _).symm ..
   · exact he i j
   simp_rw [wide,scope,widen,treats,linearCombination_single, Pi.smul_apply, peel_r,smul_zero]; exact isBigO_zero _ _ -- edit
lemma budget_triple {p:Curly G}(hp:p∈tripleSpan G)(H:∀ k,∀ i j:Hair G,i.2≠j.2→ (M k).cov (.inr i) (.inr j)=0)(h:∀ i j:α,Ripe q (fun k=>(M k).cov (.inl i) (.inl j)) 0)(g:∀ (i:Hair G)(j:α),Ripe q (fun k=>w k*(M k).cov (.inr i) (.inl j)) 0): Ripe q (fun k=> w k^3 * shock (M k) (co P*coda p)) 0:= by
   exact (ripe_mind (q:=q) (fun k=>wide (w k) (M k)) (windy M w h g) (co P*coda p)).congr_left fun k=>(cush P (w k) hp (H k)).symm
end YM.PositionX.Hinge
