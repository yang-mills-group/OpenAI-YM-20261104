import YM.Pert.Rigid.Camera
import YM.FormalOPE.RG10.Gazebo.Entries
/-! # Frozen is the hypothesis we still need in the free ON-shell spaces (>4).
Translate to our specific derivative test-network injectivity. No assumption pole.Map ordering. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k n:ℕ}(h:d≤k)
local notation "𝓕" d=> FrameAt (Deck F d) ℝ
local notation "𝒩" d=> tents F d
local notation "α"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) (PertExtension.Physical.Profile.n)

open Pert.Position
open Pert.RawLabels (enroll) -- overload
-- syntax unknown
lemma staircase : (↑(LinearMap.range (higher F h)):Set (E F k))=Pert.Position.stair F d k:= by
 ext i; constructor
 · rintro ⟨x,rfl⟩
   let p:= Pert.RawLabels.physicalLabel F d x; have he: Pert.RawLabels.enroll F d p=x:= Pert.RawLabels.physical_round F x
   refine ⟨raiseLabel G h p,?_,p.property⟩
   apply writes_inj F k; rw [writes_higher, ← he]; exact (form F k (raiseLabel G h p)).trans (form F d p).symm
 rintro ⟨x,rfl,hx⟩; let p:Labels.Label G d:=⟨x.val,hx⟩; use sourceAt F d p; apply writes_inj F k; rw [writes_higher]; exact (form F d p).trans (form F k x).symm
local notation "φ"=> Physical.operator (L:=Maxwell.standard F) (deck F d)
private abbrev push (A:𝒩 d) : Module.End ℂ (E F d) := φ A.val
lemma stages (A:𝒩 k) (x : E F d): push A (higher F h x)= higher F h (push (ρ h A) x):= by
 let H:= no_pass h ((votes _).1 (pinned _ |>.1 A.property).1).1
 let c:= Deck.climb F h; let b:= deck F d; let B:=deck F k; let g:=push A; let f:= push (ρ h A); let p:=higher F h
 have he:g.comp p=p.comp f:= by
   apply b.ext; intro i; rw [LinearMap.comp_apply,LinearMap.comp_apply,show p (b i)=B (c i) from cabin ..]
   rw [show g (B (c i))= Physical.columns B A.val _ from Physical.operator_basis (L:=Maxwell.standard F) _ A.val _, show f (b i)= Physical.columns b (ρ h A).val _ from Physical.operator_basis (L:=Maxwell.standard F) _ (ρ h A).val _ ]
   unfold columns; rw [map_sum]; simp_rw [map_smul, show ∀ i:Deck F d,p (b i)= _ from fun i=> cabin F h i]
   let C (j:Deck F k):= (A.val (c i) j:ℂ) • (B j); change ∑j,C j=∑ j,C (c j)
   conv_rhs => rw [← sum_image (f:=C) (by exact (climb_inj F h).injOn)] -- avoid local f? no
   symm; apply sum_subset (subset_univ _); intro j _ hj; unfold C; rw [show A.val (c i) j=0 from H i j (by simpa [c] using hj),Complex.ofReal_zero,zero_smul]
 exact LinearMap.congr_fun he x

lemma push_bar (A:𝒩 d): LinearMap.comp (σ₁₃:=starRingEnd ℂ) ((freeTable F).conj (table_spin F) d) (push A) = LinearMap.comp (σ₁₃:=starRingEnd ℂ) (push A) ((freeTable F).conj (table_spin F) d):= by
 apply (deck F d).ext; intro i; simp only [LinearMap.comp_apply,deck_real]; rw [show push A (deck F d i)= Physical.columns (deck F d) A.val _ from Physical.operator_basis (L:=Maxwell.standard F) _ A.val _]; unfold columns; simp_rw [map_sum,map_smulₛₗ, deck_real, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]

def buf (A:𝒩 d) : Pert.Position.Buffer F d:= ⟨(push A |>.restrictScalars ℝ).toContinuousLinearMap,by
 obtain ⟨he,hu⟩:= (pinned _).1 A.property
 refine ⟨?_, fun e he p hp=>?_, fun p=> LinearMap.congr_fun (push_bar A) p, fun (s:Signed) p=>Eq.symm (DFunLike.congr_fun (he.signed s) p), fun p=> map_smul (push A) Complex.I p⟩
 · rw [← ground]; change push A _=0; rw [show push A (deck F d _)= Physical.columns (deck F d) A.val (Deck.start F d) from Physical.operator_basis (L:=Maxwell.standard F) _ A.val _]
   unfold Physical.columns; rw [hu]; simp
 change p∈((Pert.Position.lower F e d): Set _) at hp; change push A p∈ ((Pert.Position.lower F e d): Set _); rw [←stairs_eq,← staircase he.le] at hp ⊢; obtain ⟨p,rfl⟩:=hp; exact ⟨_, (stages he.le A p).symm⟩⟩

lemma loyalty (A:𝒩 d) : buf A=0 → A=0 := by
 intro h; ext i j
 let b:=deck F d
 have hx i : (∑ j,(A.val i j:ℂ) • (b j))= (0:E F d):= by
   rw [show (∑ j,(A.val i j:ℂ) • (b j))=(buf A).val (b i) from (Physical.operator_basis (L:= Maxwell.standard F) b A.val i).symm, h]; rfl
 have hh:= congr_arg (fun u=> b.repr u j) (hx i)
 simp_rw [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,Module.Basis.repr_self,map_zero,Finsupp.single_apply] at hh; apply Complex.ofReal_injective; simpa using hh
end YM.FormalOPE.RG10.Gazebo
