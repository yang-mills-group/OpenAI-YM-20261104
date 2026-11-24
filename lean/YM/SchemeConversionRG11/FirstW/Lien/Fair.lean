import YM.SchemeConversionRG11.FirstW.Due.Zero
/-! The local interpolation bill. Rebased quadratics only (sheared, raw). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {j l m k d : ℕ}
def census (G : Gauge) (k : ℕ): Submodule ℂ (Labels.Pol G):= weightedHomogeneousSubmodule ℂ (fun _=> (1:ℕ)) k
def vault (G : Gauge) (j k : ℕ): Submodule ℂ (Labels.Pol G):= (Labels.limited G j) ⊓ census G k ⊓ LinearMap.ker ((Labels.changed (rebase G)).toLinearMap-LinearMap.id)
abbrev Reel (G : Gauge) := vault G 6 2
lemma vaulted {p : Labels.Pol G} : p ∈ vault G j k ↔ p∈Labels.limited G j ∧ IsWeightedHomogeneous (fun _=>(1:ℕ)) p k ∧ Labels.changed (rebase G) p=p := by
 unfold vault census; simp only [Submodule.mem_inf,LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,AlgHom.toLinearMap_apply,sub_eq_zero, and_assoc]; rfl -- j undeclared
lemma room (a b k : ℕ) (h:a≤b) : vault G a k ≤ vault G b k := fun x hx=> by
 obtain ⟨u,y,h⟩:= vaulted.mp hx; exact vaulted.mpr ⟨MvPolynomial.restrictSupport_mono ℂ (fun s hs=>show Labels.height s≤b from le_trans hs ‹a≤b›) u,y,h⟩
lemma fullMult {p q : Labels.Pol G} {a b r s:ℕ} (hp:p∈vault G a r) (hq:q∈vault G b s) : p*q∈vault G (a+b) (r+s) := by
  obtain ⟨t,f,H⟩:= vaulted.mp hp; obtain ⟨u,g,e⟩:= vaulted.mp hq
  refine vaulted.mpr ⟨(mem_restrictSupport_iff ℂ).2 ?_,f.mul g,by rw [map_mul,H,e]⟩ -- .mul?
  intro k hk
  have he: ∃ l m, l∈p.support ∧ m∈q.support ∧ l+m=k := by
    by_contra! h
    apply mem_support_iff.mp hk
    rw [coeff_mul]; refine Finset.sum_eq_zero fun v hv=>?_
    by_cases e:v.1∈p.support; · exact mul_eq_zero_of_right _ (not_ne_iff.mp (mem_support_iff.not.mp (fun i=> h v.1 v.2 e i (Finset.HasAntidiagonal.mem_antidiagonal.mp hv)))) -- arguments
    rw [not_ne_iff.mp (mem_support_iff.not.mp e),zero_mul]
  obtain ⟨u,v,hu,hv,E⟩:=he;change Labels.height k≤_; rw [←E,Labels.height, map_add]; exact add_le_add ((mem_restrictSupport_iff ℂ).1 ‹_› hu) ((mem_restrictSupport_iff ℂ).1 ‹_› hv)
abbrev Music (G : Gauge) (k : ℕ) := (i:Fin (k+1)) → Sol G.Color i.val
def scoreW (k : ℕ) : Labels.Jet G→ₗ[ℝ] Music G k := LinearMap.pi fun i=> sendTo G _ ∘ₗ LinearMap.proj i.val
def stageW (G : Gauge) : Field4 G→ₗ[ℝ] Labels.Jet G:= LinearMap.pi fun i=> Bare.wideLinear G i 1 0
def flute (k) : Field4 G →ₗ[ℝ] Music G k:= scoreW k ∘ₗ stageW G
def note1 {j} (L : Low (Sol G.Color j)) := emblem G j (L ∘ₗ sendTo G j)
lemma flare {j} (L : Low (Sol G.Color j)) (A : Labels.Jet G): Labels.read A (note1 L) = ↑(L (sendTo G _ (A j))) := emblem_read ..
lemma note_size {j} (L : Low (Sol G.Color j)): note1 L∈vault G (j+2) 1 := by
 let q:= L ∘ₗ sendTo G j
 refine vaulted.mpr ⟨(mem_restrictSupport_iff ℂ).2 ?_, gradientEmblem (fun _=> (1:ℕ)) q,Labels.eval_ext _ _ (fun A=>?_)⟩
 · intro t ht; exact (gradientEmblem (fun i=>i+2) q (mem_support_iff.mp ht)).le
 rw [Labels.eval_changed,flare, flare]; apply congrArg Complex.ofReal; apply congrArg _; exact sends_back _
lemma flutist (L : Low (Music G k)) : ∃ p:vault G (k+2) 1,∀ A:Labels.Jet G,Labels.read A p.val=(↑(L (scoreW k A)):ℂ) := by
 let w:= Sol G.Color; let I:=Fin (k+1); let β (i:I):w i.val →ₗ[ℝ] Music G k:=LinearMap.single ℝ (fun j:I=>w j.val) i
 let p := ∑ i:I,note1 (G:=G) (L.comp (β i))
 have hp:p∈ vault G (k+2) 1:=Submodule.sum_mem _ fun i _=>room _ _ _ (Nat.add_le_add_right (Nat.lt_succ_iff.mp i.isLt) _) (note_size _)
 refine ⟨⟨p,hp⟩,fun A=>?_⟩
 change Labels.read A p=_; unfold p; rw [map_sum]; simp_rw [flare]
 let R:=scoreW k A; change _=(↑(L R):ℂ)
 rw [show R=∑ i:I,β i (R i) from by ext1 i; erw [Finset.sum_apply]; change R i=∑ j:I,β j (R j) i; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; simp [β]; intro t _ h; simp [β,Ne.symm h]]; rw [map_sum,Complex.ofReal_sum];rfl
set_option maxHeartbeats 420000 in
private lemma recital_basis {a b:ℕ} (L : Music G a→ₗ[ℝ] Music G b→ₗ[ℝ] ℂ){I J:Type} [Fintype I][Fintype J] (u: Module.Basis I ℝ (Music G a)) (v:Module.Basis J ℝ (Music G b)): ∃ p:vault G (a+b+4) 2,∀ A:Labels.Jet G,Labels.read A p.val= L (scoreW a A) (scoreW b A) := by
  choose f F using fun i => flutist (G:=G) (k:=a) (u.coord i); choose g H using fun i => flutist (G:=G) (k:=b) (v.coord i)
  let p := ∑ i,∑ j, C (L (u i) (v j)) * ((f i).val*(g j).val)
  have hp : p∈vault G (a+b+4) 2 := by
    apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; rw [C_mul']; apply Submodule.smul_mem; apply room _ _ _ (by omega : a+2+(b+2)≤a+b+4); exact fullMult (r:=1) (s:=1) (p:=(f i).val) (q:=(g j).val) (a:=a+2) (b:=b+2) (f i).property (g j).property
  refine ⟨⟨p,hp⟩,fun A=>?_⟩
  change Labels.read A p=_
  have hh (x: Music G a) (y:Music G b): L x y=∑ i,∑ j,L (u i) (v j)*(↑(u.coord i x)*↑(v.coord j y)) := by
    nth_rw 1 [←u.sum_repr x,←v.sum_repr y]; simp only [map_sum,map_smul,LinearMap.smul_apply,LinearMap.sum_apply, Complex.real_smul, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; change _=L (u i) (v j)*(↑(u.repr x i)*↑(v.repr y j)); ring
  unfold p; rw [hh _ _]; simp only [map_sum,map_mul,F,H]; simp [Labels.read]
set_option synthInstance.maxHeartbeats 240000 in
lemma recital {a b:ℕ} (L : Music G a→ₗ[ℝ] Music G b→ₗ[ℝ] ℂ): ∃ p:vault G (a+b+4) 2,∀ A:Labels.Jet G,Labels.read A p.val= L (scoreW a A) (scoreW b A) := by
 letI free (d : ℕ) : Module.Free ℝ (Music G d) := @Module.Free.of_divisionRing ℝ _ _ _ _
 letI finite (d:ℕ) : Module.Finite ℝ (Music G d) := by unfold Music; infer_instance
 exact recital_basis L (Module.finBasis ℝ _) (Module.finBasis ℝ _)
-- polarization evaluations. will agree with 1/2! derivative loot.
def sun (x : Field4 G) := Labels.read (stageW G x)
def chord (x y:Field4 G) : Labels.Pol G→ₗ[ℂ] ℂ := (1/2:ℂ) • ((sun (x+y)).toLinearMap- (sun x).toLinearMap-(sun y).toLinearMap)
lemma chord_at (x y:Field4 G) (p:Labels.Pol G) : chord x y p = (1/2)*(sun (x+y) p -sun x p-sun y p) := rfl
lemma chord_com (x y:Field4 G) : chord x y=chord y x := LinearMap.ext (fun p=>by rw [chord_at,chord_at,add_comm x]; ring)
end YM.RG11.FirstW
