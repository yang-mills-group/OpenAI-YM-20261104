import YM.SchemeConversionRG11.FirstW.Lien.Chips
import YM.Push.FINITE_DETECTION.NoLinear
/-! Average ON COLOR only, so interpolation landing still on the same Adjoint/taylor coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {j k : ℕ}
def smock (G : Gauge) := Reel G ⊓ Labels.invariantSpace G
abbrev Paper (G : Gauge):= ↥(smock G)
abbrev mimic (u : G.El) : Labels.Pol G →ₐ[ℂ] Labels.Pol G:= Labels.changed fun _=> Labels.Taylor.paint u
lemma change_weight (p:Labels.Pol G) (hp:p∈census G k) (Z : applyJet G) : Labels.changed Z p∈census G k := by
 let L := fun _ : Labels.Key G=> (1:ℕ)
 refine gradeMove L L (Labels.changed Z) (fun i=>?_) p k hp
 rw [Labels.changed,aeval_X]; apply IsWeightedHomogeneous.sum; intro a _; apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X ℂ L ⟨i.1,a⟩
lemma steady (u : G.El) (p:Labels.Pol G): Labels.changed (rebase G) (mimic u p)=mimic u (Labels.changed (rebase G) p) := Labels.eval_ext _ _ (fun A=> by
 simp only [mimic,Labels.eval_changed]; refine congrArg (fun q=>Labels.read q p) ?_; funext i; exact (rebase_color u _).symm)
def colorsP (u : G.El) (p: Reel G): Reel G:= ⟨mimic u p.val, by
 obtain ⟨t,f,e⟩:= vaulted.mp p.property; apply vaulted.mpr; exact ⟨Labels.moved_limit t _,change_weight p.val (show p.val ∈ census G _ from f) _,by rw [steady,e]⟩⟩
private instance reelfin : FiniteDimensional ℂ (Reel G):= FiniteDimensional.of_injective
  (Submodule.inclusion (show Reel G≤ Labels.limited G 6 from fun _ hp=> (vaulted.mp hp).1)) (Submodule.inclusion_injective _)
abbrev readP (A: Labels.Jet G): Reel G →ₗ[ℂ]ℂ:= (Labels.read A).toLinearMap.comp (Reel G).subtype
lemma reports_continuity (p:Reel G) (B : Reel G→ₗ[ℂ]ℂ) : Continuous (fun u:G.El=> B (colorsP u p)) := by
  have ht : B∈ Submodule.span ℂ (Set.range (readP (G:=G))) := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=Submodule.span ℂ (Set.range _)),Submodule.mem_dualAnnihilator]; intro x hx
    have he:= (Submodule.mem_dualCoannihilator _).mp hx
    have h : x= (0:Reel G) := Subtype.ext (Labels.eval_ext _ _ fun A=> (he _ (Submodule.subset_span ⟨A,rfl⟩)).trans (Labels.read A|>.map_zero.symm)) -- syntax
    rw [h,map_zero]
  induction ht using Submodule.span_induction with
  | zero=>exact continuous_const
  | add x y _ _ i j=> exact i.add j
  | smul r x _ i=> exact i.const_smul r
  | mem x hx=>
    obtain ⟨A,rfl⟩:=hx
    change Continuous (fun u:G.El=> Labels.read A (mimic u p.val))
    simp only [mimic, Labels.eval_changed]; change Continuous (fun u:G.El=>Labels.read (Labels.colored u A) p.val)
    generalize h:p.val=q
    clear p h
    induction q using MvPolynomial.induction_on with
    | C c=> simp only [Labels.read,aeval_C]; exact continuous_const
    | add p q i j=> simp only [map_add]; exact i.add j
    | mul_X p a i=> simp only [map_mul]; apply i.mul; simp only [Labels.read, aeval_X]; exact Push.FiniteDetection.Low.coord_cont ..
lemma tablet (p : Reel G) : ∃ q : Reel G,∀ B : Reel G→ₗ[ℂ]ℂ,B q= ∫ v:G.El,B (colorsP v p) ∂G.probHaar := by
  letI := @Module.Free.of_divisionRing ℂ (Reel G) _ _ _
  let b:= Module.finBasis ℂ (Reel G)
  refine ⟨∑ i,(∫ v:G.El,b.coord i (colorsP v p) ∂G.probHaar) • b i,fun B=>?_⟩
  have hh (u:Reel G): B u=∑ i, b.coord i u * B (b i) := by nth_rw 1 [← b.sum_repr u]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> B.map_smul ..
  simp_rw [show ∀ v:G.El,B (colorsP v p)=_ from fun v=>hh (colorsP v p)]; rw [integral_finsetSum]
  · simp only [map_sum,map_smul,smul_eq_mul,integral_mul_const]
  intro i _; exact (reports_continuity p (b.coord i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) |>.mul_const _
lemma painting (x : Labels.Jet G) (u : G.El) (v : Reel G) : readP x (colorsP u v)= Labels.read (Labels.colored u x) v.val:= by change Labels.read x (Labels.changed (fun _=> Labels.Taylor.paint u) v.val)=_; rw [Labels.eval_changed];rfl
lemma tabulated (p : Reel G) : ∃ q: Paper G,∀ B: Reel G →ₗ[ℂ] ℂ,B (⟨q.val,q.property.1⟩:Reel G)=∫ v:G.El,B (colorsP v p) ∂G.probHaar := by
  obtain ⟨q,H⟩:=tablet p
  have hp(v u:G.El)(x:Labels.Jet G): Labels.colored v (Labels.colored u x)=Labels.colored (v*u) x := funext (fun i=> Labels.Taylor.value_ext _ _ (funext fun j=> funext fun z=> (G.adjoint_mul v u ((x i).value j z)).symm))
  have ht : q.val∈ Labels.invariantSpace G:= by
    intro A u; change readP (Labels.colored u A) q=readP A q; rw [H,H]; simp_rw [painting,hp]; exact integral_mul_right_eq_self (fun s=>Labels.read (Labels.colored s A) p.val) _
  exact ⟨⟨q.val,q.property,ht⟩,H⟩
lemma testedColor (p:Reel G) (u:G.El)(A B: Field4 G): chord A B (colorsP u p).val=chord (putting u A) (putting u B) p.val := by
  have he (A:Field4 G): sun A (colorsP u p).val=sun (putting u A) p.val:=by rw [show sun A (colorsP u p).val=readP _ (colorsP u p) from rfl,painting]; exact congr_arg (fun q=>Labels.read q p.val) (show Labels.colored u (stageW G A) = stageW G (putting u A) from funext fun i=>(letter_key ..).symm)
  rw [chord_at,chord_at,he,he,he, map_add]
end YM.RG11.FirstW
