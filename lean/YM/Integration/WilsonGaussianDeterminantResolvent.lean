import YM.Integration.WilsonGaussianDeterminantBooks

/-! Actual color diagonal resolvent on each prescribed finite Gaussian window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantResolvent

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open WilsonGaussianDeterminantVertex

variable {W s μ C : ℝ} {R : Rep G f} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}


def entry {B : ℕ} (D : Window (along (G:=G) S) B) (A : Itinerary.Mat f G) (k : Tubular f G) : ℝ :=
  let I := D.take k
  let r : I := ⟨k,D.here k⟩
  ∫ u in (0:ℝ)..1, ((Batch.principal I (A-1)) * (Batch.principal I (1+u • (A-1)))⁻¹) r r

theorem entry_eq {B : ℕ} (D : Window (along (G:=G) S) B) (A : Itinerary.Mat f G) (k : Tubular f G) :
    entry D A k = localBase D A k := by
  unfold entry localBase lact
  apply intervalIntegral.integral_congr
  intro u _
  exact (Batch.perWindow A D k u rfl (D.here k)).symm

def independent (X : Coat T F) (i : Bond f) (u : ZipP G c f) : ℝ :=
  let Y := Pavilion.drip X u
  ((∑ k : G.ColorIndex, entry Y.shutter Y.blank.plate (i,k)) -
    ∑ k : G.ColorIndex, entry Y.shutter Y.plate (i,k))/2

theorem identity (X : Coat T F) (i : Bond f) : independent X i = Pavilion.stag X i := by
  funext u
  simp only [independent,entry_eq,Pavilion.stag,Coat.condensation,Batch.joint]

theorem at_origin (X : Coat T F) (i : Bond f) : independent X i 0 = 0 := by
  rw [identity]
  have h : Pavilion.drip X (0 : ZipP G c f) = (X.wrapY 1).blank := by
    unfold Pavilion.drip dry
    dsimp only [Prod.fst_zero]
    rw [Work.G07.at_zero_increment]
    rfl
  unfold Pavilion.stag Coat.condensation
  rw [h]
  rw [show ((X.wrapY 1).blank).blank = (X.wrapY 1).blank from rfl,sub_self,zero_div]

private theorem ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → ℝ) (v : E) (n : ℕ) (ha : ContDiffAt ℝ n a 0) :
    iteratedDeriv n (fun z : ℝ => a (z • v)) 0 =
      iteratedFDeriv ℝ n a 0 (fun _ => v) := by
  let l : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have ha' : ContDiffAt ℝ n a (l 0) := by simpa only [map_zero] using ha
  have hπ := blockTaylor_contDiff n a (n : WithTop ℕ∞)
  have hc := jets_comp (f := (l : ℝ → E)) (f' := (l : ℝ → E))
    (g := a) (g' := blockTaylor n a) l.contDiff.contDiffAt l.contDiff.contDiffAt
    ha' hπ.contDiffAt rfl (fun _ _ => rfl)
    (fun k hk => by simpa only [map_zero] using (blockTaylor_jets ha k hk).symm) n le_rfl
  change iteratedFDeriv ℝ n (a ∘ l) 0 (fun _ => 1) = _
  rw [hc,l.iteratedFDeriv_comp_right hπ 0 le_rfl,map_zero,blockTaylor_jets ha n le_rfl]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,l]

def reading (n : ℕ) (X : Coat T F) (i : Bond f) (v : ZipP G c f) : ℝ :=
  if voyage X.seeds (200 * X.B) i then 0 else
    (n.factorial : ℝ)⁻¹ * iteratedDeriv n (fun t : ℝ => independent X i (t • v)) 0

theorem same (n : ℕ) (X : Coat T F) (i : Bond f) (v : ZipP G c f)
    (h : ContDiffAt ℝ n (Pavilion.stag X i) 0) : coefficient n X i v = reading n X i v := by
  rw [reading,identity,ray (Pavilion.stag X i) v n h]
  rfl

theorem paid (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (v : ℝ → ℝ) (L : Side) (hv : Rate G L (-(1/2)) v) (hu : ∀ᶠ x : ℝ in atTop, 0 ≤ v x)
    (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (μ C : ℝ)
      (_ : Cash W s μ L Q o C T R) (F : Forest S.ratio) (X : Coat T F) (i : Bond f),
      S.patch=D → X.x=s → X.width=o.K → ∀ n ≤ p, ∀ u, coefficient n X i u = reading n X i u := by
  obtain ⟨_, _, h⟩ := Pavilion.bazaar P Q o v L hv hu D hD (p+1) (Nat.succ_pos p)
  filter_upwards [h,hu] with s hs hs₀
  intro c f S T R μ C H F X i h₁ h₂ h₃ n hn u
  have hb := hs c f S T R μ C H F X i h₁ h₂ h₃ 0 (by rwa [norm_zero])
  exact same n X i u (hb.2.smaller (hn.trans (Nat.le_succ _))).smooth

end YM.Integration.WilsonGaussianDeterminantResolvent
end
