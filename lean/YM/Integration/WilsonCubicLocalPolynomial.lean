import YM.Integration.WilsonCubicOriginalTorus

/-! The retained physical polynomial of each protected path, in the
finite-torus coefficient coordinates used for the independently filed
action. The original protector and its evaluation argument stay in place. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCubicLocalPolynomial
open Filter Function Finset Lattice RG Wilson Pressure Pressure.Tube Push Tree Precision Exterior
open Stationary Work.G05 ConnectedActivityE6 SliceRows Coat Blaze Frond
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Near
open WilsonCoeffUV.Blue
open Push.AbsoluteSums Next.Fluctuations SectorMeasure Oriented Work.E03
open Shell Control Pulse Footprint Raw Matter Window Mask Blaze.March Captain Silica Pond Poll Tablet
open Eider Stained Shield Flux Brush Scroll Vine Art Polar Foramen Gate Quill Hues
open Rotation Progress.StationaryScenes LocalTaylorR2 LocalTaylorR2.Kiln Axial Channel Canvas
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def letters (S : StepData c f) (z : ZipP G c f) : Link G f :=
  WilsonCubicOriginalTorus.coordinates G f (fun e => G.plog (G.mat (shaft S z e)))

private theorem origin (S : StepData c f) : shaft S (0 : ZipP G c f) = 1 := by
  funext e
  simp [shaft,RG.increment,replica,G.mat_lieExp_zero]

private theorem links (S : StepData c f) (e : Bond f) :
    ContDiffAt ℝ ω (fun z : ZipP G c f => G.mat (shaft S z e)) 0 := by
  have fine : ContDiff ℝ ω (fun z : ZipP G c f => G.mat (G.lieExp (z.2 e))) :=
    G.exp_jet.comp (((ContinuousLinearMap.proj e : Directions G f →L[ℝ] G.Color).contDiff).comp contDiff_snd)
  have coarse (i : Bond c) : ContDiff ℝ ω (fun z : ZipP G c f => G.mat (G.lieExp (z.1 i))) :=
    G.exp_jet.comp (((ContinuousLinearMap.proj i : Directions G c →L[ℝ] G.Color).contDiff).comp contDiff_fst)
  by_cases h : S.ratio.parent (e.1+step e.2)=S.ratio.parent e.1
  · simpa [shaft,RG.increment,replica,h] using fine.contDiffAt (x:=0)
  · simpa [shaft,RG.increment,replica,h,G.mat_mul] using (fine.mul (coarse (S.ratio.parent e.1,e.2))).contDiffAt (x:=0)

private theorem analytic (S : StepData c f) : ContDiffAt ℝ ω (letters (G:=G) S) 0 := by
  apply (WilsonCubicOriginalTorus.coordinates G f).contDiff.contDiffAt.comp
  apply contDiffAt_pi.mpr
  intro e
  apply ContDiffAt.comp (g:=G.plog) (f:=fun z : ZipP G c f => G.mat (shaft S z e)) _ _ (links S e)
  simpa only [origin,Pi.one_apply,G.mat_one] using G.plog_diff

private theorem recovered (S : StepData c f) :
    shaft S =ᶠ[𝓝 (0 : ZipP G c f)] fun z => Stationary.input G f (letters S z) := by
  have every (e : Bond f) : ∀ᶠ z in 𝓝 (0 : ZipP G c f),
      G.lieExp (G.plog (G.mat (shaft S z e))) = shaft S z e := by
    have h : ContinuousAt (fun z : ZipP G c f => shaft S z e) 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
        (links S e).continuousAt.tendsto
    have toOne := h.tendsto
    rw [origin,Pi.one_apply] at toOne
    exact toOne.eventually G.plog_right
  filter_upwards [eventually_all.mpr every] with z hz
  change shaft S z=represent (arm G f 1 ((arm G f 1).symm _))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change shaft S z=represent (toLog fun e => G.plog (G.mat (shaft S z e)))
  rw [edits]
  funext e
  simp [RG.increment,hz]

def reader {j : ℕ} (A : ℕ → Atom G j) (i : Trans f) (u : Link G f) : ℝ :=
  (A i.2.2).unmasked (pull i.1 0 (Stationary.input G f u)) i.2.1

def filed {j : ℕ} (A : ℕ → Atom G j) (i : Trans f) (r : ℕ) (u : Link G f) : ℝ :=
  ∑ k ∈ Finset.range (r+1), MvPolynomial.eval u (PowerSeries.coeff k (jet (reader A i)))

theorem issued {j : ℕ} (A : ℕ → Atom G j) (i : Trans f) :
    reader A i = Near.meter (A i.2.2) i.2.1 ∘ orderTurn (G:=G) i.1 := by
  funext u
  simp [reader,Near.meter,orderTurn,flip_links]

private theorem regular {j : ℕ} (A : ℕ → Atom G j) (i : Trans f) : ContDiffAt ℝ ω (reader A i) 0 := by
  rw [issued]
  exact ((Near.meter_hot _ _).comp (orderTurn (G:=G) (m:=f) i.1).contDiff).contDiffAt

private theorem printed {j : ℕ} (A : ℕ → Atom G j) (i : Trans f) (r : ℕ) :
    filed A i r = blockTaylor r (reader A i) := by
  funext u
  unfold filed blockTaylor
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => rayon _ _ _

private theorem polynomial {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {A B : E → ℝ}
    (h : ∀ i ≤ d, iteratedFDeriv ℝ i A 0 = iteratedFDeriv ℝ i B 0) :
    blockTaylor d A = blockTaylor d B := by
  unfold blockTaylor
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Tensor.coeff,h i (by omega)]

theorem kept {j : ℕ} (J : Basecamp G) (X : Coat T F) (A : ℕ → Atom G j)
    (i : Trans f) (r : ℕ) (u : Directions G f) :
    pollen J X A i r u =
      blockTaylor r (filed A i r ∘ blockTaylor r (letters S)) (argument J X A i u) := by
  let g := reader A i
  let h := letters (G:=G) S
  have same : latent A S i =ᶠ[𝓝 (0 : ZipP G c f)] g ∘ h := (recovered S).mono fun z hz =>
    congrArg (fun U => (A i.2.2).unmasked (pull i.1 0 U) i.2.1) hz
  have z0 : h 0 = 0 := by
    have he : (fun e => G.plog (G.mat (shaft S (0 : ZipP G c f) e))) = (0 : Directions G f) := by
      funext e
      simp [origin]
    exact (congrArg (WilsonCubicOriginalTorus.coordinates G f) he).trans (map_zero _)
  have a : ContDiffAt ℝ r h 0 := (analytic S).of_le le_top
  have b : ContDiffAt ℝ r g 0 := (regular A i).of_le le_top
  have h0 : blockTaylor r h 0=0 := (blockTaylor_zero r h).trans z0
  have cj := jets_comp (x:=0) (g:=g) (g':=blockTaylor r g) a (blockTaylor_contDiff r h _).contDiffAt
    (z0.symm ▸ b) (blockTaylor_contDiff r g _).contDiffAt (z0.trans h0.symm)
    (fun k hk => (blockTaylor_jets a k hk).symm)
    (fun k hk => by rw [h0]; exact (blockTaylor_jets b k hk).symm)
  have jets (k) (hk : k≤r) := ((same.iteratedFDeriv ℝ k).eq_of_nhds).trans (cj k hk)
  rw [Kiln.pollen,printed,polynomial jets]

end YM.Integration.WilsonCubicLocalPolynomial
