import YM.X.Reed.Oka
/-!
# Lattice 1-form probes with differential orders. Finite support throughout. Joint components.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Next.Rank.Beamer Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell Asymptotics
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {n k m d:ℕ}
abbrev Fan (G:Gauge):= Hair G →₀ ℝ
def flatL (A:Brush G): Fan G→ₗ[ℝ] ℝ:= Finsupp.linearCombination ℝ (text A)
lemma flat₁ (x:Brush G)(z:Hair G): flatL x (Finsupp.single z 1)=text x z:= by unfold flatL;rw [Finsupp.linearCombination_single,one_smul]
def taste : Fan G→ₗ[ℝ] Brush G→ₗ[ℝ] ℝ:= Finsupp.linearCombination ℝ (fun i:Hair G=> (EuclideanSpace.proj i.2).toLinearMap ∘ₗ LinearMap.proj i.1)
lemma taste_eval (A:Brush G)(z:Fan G): taste z A=flatL A z:= by
    induction z using Finsupp.induction_linear with
    | zero=> simp
    | add a b h g=> simp [h,g]
    | single i c=> unfold flatL taste; rw [Finsupp.linearCombination_single,Finsupp.linearCombination_single];rfl
lemma all_hair (f:Module.Dual ℝ (Fan G)) : ∃ x:Brush G,f=flatL x:= by
    let x:= textL.symm (fun z:Hair G=> f (Finsupp.single z 1)); refine ⟨x,?_⟩; ext z; simp only [LinearMap.comp_apply,Finsupp.lsingle_apply]; rw [flat₁]; rfl -- maybe ext z yields scalar?
lemma fanSpan (P:Submodule ℝ (Fan G)) {x:Fan G} : x∈P ↔ ∀ s:Brush G,(∀ f∈P,flatL s f=0)→flatL s x=0 := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]; constructor
    · intro h s hs; exact h _ ((Submodule.mem_dualAnnihilator _).mpr hs)
    intro h f hf; obtain ⟨A,rfl⟩:= all_hair f; exact h _ ((Submodule.mem_dualAnnihilator _).mp hf) -- namespace
lemma taste_pin (f g:Fan G)(h:∀ A,taste f A=taste g A): f=g:= by
    apply sub_eq_zero.mp; apply (show f-g∈(⊥:Submodule ℝ (Fan G)) → _ from fun y=>y);
    apply (fanSpan _).mpr; intro s _; rw [map_sub,← taste_eval,← taste_eval,h,sub_self]

def jetRow : (n:ℕ)→ (Fin n→Axis)→Hair G→Fan G
 | 0,_,z=> Finsupp.single z 1
 | n+1,l,z=> jetRow n (Fin.tail l) ((z.1.1+step (l 0),z.1.2),z.2)- jetRow n (Fin.tail l) z
lemma jets_row (x:Brush G)(v:Hair G)(l:Fin n→Axis): flatL x (jetRow n l v)= jumped l (raising v.1.2 x) v.1.1 v.2:= by
    induction n generalizing v with
    | zero=>exact flat₁ x v
    | succ n ih=> rw [jetRow,map_sub,ih,ih,jumpIt l,jumps,hopped]; rfl

-- exact differential order n. implies lower order

def grads (G:Gauge)(n:ℕ): Submodule ℝ (Fan G):= Submodule.span ℝ (Set.range (uncurry (jetRow n)))
lemma grad_row (l:Fin n→Axis)(v:Hair G): jetRow n l v∈grads G n:= Submodule.subset_span ⟨(l,v),rfl⟩
lemma grad_retract (p:n≤k): grads G k≤grads G n:= by
    induction p with
    | refl=>exact le_rfl
    | step he ih=>
       apply le_trans _ ih; apply Submodule.span_le.mpr; rintro _ ⟨⟨l,v⟩,rfl⟩; unfold Function.uncurry; rw [jetRow]; exact Submodule.sub_mem _ (grad_row _ _) (grad_row _ _)
def Cloudless (n:ℕ)(x:Brush G): Prop:= ∀ l:Fin n→Axis, ∀ j:Axis,jumped l (raising j x)=0
lemma cloud_ann (y:Fan G) : y∈grads G n ↔ ∀ s:Brush G, Cloudless n s→flatL s y=0 := by
    let P:=grads G n; have he(s:Brush G) : (∀ f∈P,flatL s f=0)↔ Cloudless n s:= by
       constructor
       · intro h l i; funext z; apply PiLp.ext; intro j; exact (jets_row s ((z,i),j) l).symm.trans (h _ (grad_row _ _))
       intro h f hf; exact (show P ≤ LinearMap.ker (flatL s) from Submodule.span_le.mpr (by rintro _ ⟨⟨l,v⟩,rfl⟩; change flatL s (jetRow _ l v)=0; rw [jets_row,h];rfl)) hf -- `P ≤` uses implicit intro mismatch
    change y∈P ↔_;rw [fanSpan]; simp_rw [he]
lemma cloud_rise {x:Brush G}(h:Cloudless n x)(hk:n≤k): Cloudless k x:= by
    intro l i; funext z; apply PiLp.ext; intro j; exact (jets_row x ((z,i),j) l).symm.trans ((cloud_ann _).mp (grad_retract hk (grad_row _ _)) x h)
lemma vanish_step (x:Fan G)(h:x∈grads G n) (j:Specs G k)(hk:k<n): flatL (port k j) x=0:= (cloud_ann _).mp h _ (fun l w=> larger j w hk l)
lemma grade0 : grads G 0=⊤:= by
    rw [eq_top_iff]; intro p _; refine (cloud_ann _).mpr ?_; intro s h
    have he:s=0:= funext fun x=> congr_fun (h (fun i=> Fin.elim0 i) x.2) x.1
    rw [he,← taste_eval,map_zero]
end YM.PositionX.Reed
