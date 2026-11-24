import YM.Pert.Parity.Fields
import YM.Primitives.HAAR_LOG_JETS.Symmetry
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color
import YM.Next.STATIONARY.Joint.Gauge
/-! Constant conjugations for checking density/FP jets. They preserve inversion constraints and the *mean-free* adjustment. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.Pert.First
open Filter Orb Lattice Function Topology
open scoped Topology
variable {G : Gauge} {N : Side}
variable (u : G.El)

def linkCol : Module.End ℝ (Potential G N) where
  toFun l := ⟨fun e=> G.adjoint u (l.val e), fun e=> by dsimp; rw [l.property e,map_neg]⟩
  map_add' x y := Subtype.ext (funext fun e=> (G.adjoint u).map_add ..)
  map_smul' r x := Subtype.ext (funext fun e=> LinearMap.map_smul ..)
@[simp] lemma linkCol_edge (x : Potential G N) (e) : (linkCol u x).val e=G.adjoint u (x.val e) := rfl

def paramCol : Module.End ℝ (Parameter G N) where
  toFun p := by
    refine ⟨fun e=> G.adjoint u (p.val e), (show _ ∧ _ from ⟨?_ , ?_⟩)⟩
    · intro x;dsimp; rw [p.property.1 x]
    · change G.adjoint u (p.val 0)=0; rw [show p.val 0=0 from p.property.2,map_zero]
  map_add' x y := Subtype.ext (funext fun e=> (G.adjoint u).map_add ..)
  map_smul' r x := Subtype.ext (funext fun e=> LinearMap.map_smul ..)
@[simp] lemma paramCol_site (x : Parameter G N) (e) : (paramCol u x).val e=G.adjoint u (x.val e) := rfl

def meanCol : Module.End ℝ (Mean G N) where
  toFun p := by
    refine ⟨fun e => G.adjoint u (p.val e), (show _ ∧ _ from ⟨?_ , ?_⟩)⟩
    · intro x;dsimp; rw [p.property.1 x]
    · have he : ∑ x, p.val x = 0 := by simpa [LinearMap.mem_ker,LinearMap.sum_apply,LinearMap.proj_apply] using p.property.2
      change (∑ a:Site N,LinearMap.proj (R:=ℝ) (φ:=fun _ : Site N=>G.Color) a) (fun e=>G.adjoint u (p.val e))=0; rw [LinearMap.sum_apply]; simp only [LinearMap.proj_apply,←map_sum,he,map_zero]
  map_add' x y := Subtype.ext (funext fun e=> (G.adjoint u).map_add ..)
  map_smul' r x := Subtype.ext (funext fun e=> LinearMap.map_smul ..)
@[simp] lemma meanCol_site (x : Mean G N) (e) : ((meanCol u) x).val e=G.adjoint u (x.val e) := rfl

lemma color_div (l : Links (Per N) G.Color) : divB (G.adjoint u ∘ l) = G.adjoint u ∘ (divB l) := by
  funext x; unfold divB; simp only [comp_apply,map_sum,map_sub]
lemma color_bal (l : Links (Per N) G.Color) : balance G N (G.adjoint u ∘ l) = linkCol u (balance G N l) := by
  ext1; apply funext; intro e; change (1/2:ℝ) • (G.adjoint u _)-(1/2:ℝ) • (G.adjoint u _) = G.adjoint u ((1/2:ℝ) • _-(1/2:ℝ) • _); simp
lemma color_dlin (l : Potential G N) : dLin ((linkCol u) l) = (meanCol u) (dLin l) := Subtype.ext (color_div u l.val)
lemma color_gZ (l : Parameter G N) : gZ ((paramCol u) l) = linkCol u (gZ l) := Subtype.ext (funext fun e=> by change G.adjoint u _ - G.adjoint u _ = G.adjoint u (_-_); rw [map_sub]; rfl)
lemma color_bridge (l : Parameter G N) : bridge G N (paramCol u l) = meanCol u (bridge G N l) := by simp_rw [bridge, LinearMap.comp_apply,color_gZ,color_dlin]
lemma link_cancel : Function.LeftInverse (linkCol (N:=N) u⁻¹) (linkCol u) := fun _ => Subtype.ext (funext fun e=> by simp [← G.adjoint_mul])
lemma param_cancel : Function.LeftInverse (paramCol (N:=N) u⁻¹) (paramCol u) := fun _=>Subtype.ext (funext fun e=> by simp [← G.adjoint_mul])
lemma jacobian_invariant (x : Potential G N) : Orb.Jacob (linkCol u x)=Orb.Jacob x := by
  simp only [Jacob,linkCol_edge, Primitives.HaarLogJets.spin_adjoint]
lemma turn_under (a : Potential G N) (z : Parameter G N) (l : Edge (Site N)): turn (linkCol u a) (paramCol u z) l = u*(turn a z l)*u⁻¹ := by simp only [turn,positiveLinks,linkCol_edge,paramCol_site,Stationary.adjoint_exp]; group
lemma turn_cont (l : Edge (Site N)) : Tendsto (fun p : Potential G N × Parameter G N => turn p.1 p.2 l) (𝓝 (0,0)) (𝓝 1) := by
  have hu (a : Site N) : Continuous (fun z : Parameter G N => z.val a) := (siteEval a).continuous_of_finiteDimensional
  have hv (a : Edge (Site N)) : Continuous (fun z : Potential G N => z.val a) := (takeLink a).continuous_of_finiteDimensional
  have h := (((G.lieExp_cont.comp (hu l.1)).comp continuous_snd).mul ((G.lieExp_cont.comp (hv l)).comp continuous_fst)).mul ((G.lieExp_cont.comp (hu (l.1+step l.2))).inv.comp continuous_snd)
  change Continuous (fun p : Potential G N × Parameter G N => turn p.1 p.2 l) at h
  exact turn_zero (G:=G) l ▸ h.tendsto (0,0)
end YM.Pert.First
