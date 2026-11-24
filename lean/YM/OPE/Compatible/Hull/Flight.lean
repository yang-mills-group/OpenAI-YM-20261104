import YM.OPE.Compatible.Hull.Brace
/-! # leading physical contour in normalized board. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set Lattice MeasureTheory RG Wilson Flume Flume.Page Flume.Script Gauge
open Source Labels Source.Drops Next.Rank Next.Rank.Spindle WilsonStartup
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
attribute [local instance] Drops.instNormedSpaceRealSnap
-- expedite synth
set_option synthInstance.maxHeartbeats 200000
variable {G:Gauge}{d m n b:ℕ}(H:Hol G)
noncomputable abbrev Hig (x:Snap G d):=H.links d (expand d x) 1
noncomputable abbrev LeapV (i: Edge Cover)(x:Snap G d): G.Color := indexS i (board (Hig H x))
lemma nearV (u:UsedEdges (box b)) : LeapV H u.val=ᶠ[𝓝 (0:Snap G d)] localK G ∘ (bore H d b u):=by
    let U(x:Snap G d):= Hig H x; let W(x:Snap G d):= travel (U x) 0 (ringO u.val); have ht : Tendsto W (𝓝 0) (𝓝 1):=by
       apply ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff).2; have hx: W 0=1:=by unfold W; rw[show U 0=1 from funext fun i=>(Work.G02.linkGerm H d i).2.1]; exact Pressure.one _
       rw [←hx]; exact (Work.G02.walkGerm H d _ _).1.continuousAt.tendsto
    filter_upwards [ht.eventually G.plog_right] with x hx; rw [LeapV,CurU] -- adjust
    change _= G.curvature (G.lieExp (G.plog (G.mat _))); rw [novaU]; unfold W at hx; rw [ringE] at hx; exact congr_arg G.curvature hx.symm
lemma Leap0 (u:UsedEdges (box b)): LeapV H u.val (0:Snap G d)=0:= (nearV H u).self_of_nhds.trans (by simp [bore])
lemma soar (d m:ℕ): ∃ C:ℝ, ∃ v:ℕ,0≤C∧∀ b:ℕ,∀ i:UsedEdges (box b), ContDiffAt ℝ m (LeapV H i.val) (0:Snap G d) ∧ slopeCap m (LeapV H i.val) (0:Snap G d)≤ C*(1+(b:ℝ))^v:=by
     choose C v hc HH using fun i=> shots H d i -- name
     obtain ⟨D,w,hD,h⟩:= artillery C v m hc; let F:=D+1; have hf:1 ≤ F:=le_add_of_nonneg_left hD; let K:= localK G; let T:= ∑ i∈Finset.range (m+1),slopeCap i K 0; have hT:0≤ T:=Finset.sum_nonneg fun _ _=> norm_nonneg _; refine ⟨m.factorial*T*F^m,w*m,mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) (pow_nonneg (zero_le_one.trans hf) _),fun b i=>?_⟩
     let g:= bore H d b i; let V:=K ∘ g; have he: g 0=0:=by simp [g,bore]
     have hh: ContDiffAt ℝ m g 0:=(HH m b i).1; have ht: ContDiffAt ℝ m K (g 0):= he ▸ (localK_analytic ..).of_le le_top; let X:=1+(b:ℝ); have hx:1≤ X:=le_add_of_nonneg_right (Nat.cast_nonneg _); let U:= F*X^w; have hu:1 ≤ U:=one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hx); have hb : LeapV H i.val=ᶠ[𝓝 0] V:=nearV H _
     refine ⟨(ht.comp 0 hh).congr_of_eventuallyEq hb, ?_⟩; apply (show slopeCap m (LeapV H i.val) (0:Snap G d)=slopeCap m V 0 from congr_arg norm ((hb.iteratedFDeriv ℝ m).eq_of_nhds)).trans_le; refine (strap g K 0 m hh ht T U (fun i hi=>he.symm ▸ Finset.single_le_sum (f:=fun i=>slopeCap i K 0) (fun i hi=>norm_nonneg _) (Finset.mem_range.mpr (by omega))) ?_).trans_eq ?_
     · intro j hi hk; exact ((HH _ b i).2.trans (h X hx j hk)).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (pow_nonneg (zero_le_one.trans hx) _)).trans ((pow_one U).symm.trans_le (pow_le_pow_right₀ hu hi)))
     unfold U X; rw [mul_pow,pow_mul,mul_assoc (_*_)] -- adjust
lemma pieceZ (v:Snap G d)(x:Cover)(w:Walk): Exterior.linkSum (access v) x w= (pieces (fun i : Cover×Shade G=> access v (i.1,i.2.1) i.2.2) x w).sum:=by
     induction w generalizing x with
     | nil=>rfl
     | cons i w ih=>rw [Exterior.linkSum,pieces,List.sum_cons,ih]; congr -- defeq
abbrev Sie (x:Snap G d):fieldX (Shade G):=fun i=> access x (i.1,i.2.1) i.2.2
private lemma projected_ray {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : DifferentiableAt ℝ f 0) (q : Y →L[ℝ] ℝ) (x : X) :
    HasDerivAt (fun t : ℝ => q (f (t • x))) (q (fderiv ℝ f 0 x)) 0 := by
  have ht : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using! (hasDerivAt_id' (0 : ℝ)).smul_const x
  exact q.hasFDerivAt.comp_hasDerivAt 0
    (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (by simp only [zero_smul]))

private lemma leap_differentiable (u : UsedEdges (box b)) :
    DifferentiableAt ℝ (LeapV H u.val) (0 : Snap G d) :=
  ((soar H d 1).choose_spec.choose_spec.2 b u).1.differentiableAt one_ne_zero

private lemma ray_derivative (u : UsedEdges (box b)) (x : Snap G d) (i : G.ColorIndex) :
    HasDerivAt (fun t : ℝ => LeapV H u.val (t • x) i) ((fderiv ℝ (LeapV H u.val) 0 x) i) 0 :=
  projected_ray (leap_differentiable H u) (EuclideanSpace.proj i) x

private lemma read_matrix_derivative (i : G.ColorIndex) {F : ℝ → G.Mat} {A : G.Mat}
    {g : ℝ → ℝ} (hF : HasDerivAt F A 0) (hg : ∀ t, g t = pleatsF i (F t - 1)) :
    HasDerivAt g (pleatsF i A) 0 := by
  let f : G.Mat →L[ℝ] ℝ := (pleatsF i).toContinuousLinearMap
  rw [show g = f ∘ (fun t => F t - 1) from funext hg]
  exact f.hasFDerivAt.comp_hasDerivAt 0 (hF.sub_const 1)

private lemma holonomy_read (u : UsedEdges (box b)) (x : Snap G d) (i : G.ColorIndex) :
    HasDerivAt (fun t : ℝ => LeapV H u.val (t • x) i)
      (pleatsF i (G.colorMat (Exterior.linkSum (access x) 0 (ringO u.val)))) 0 := by
  apply read_matrix_derivative i ((Work.G02.walkGerm H d (ringO u.val) 0).2 x)
  exact fun _ => (pleatsEq _ _).symm

private lemma contour_read (u : UsedEdges (box b)) (x : Snap G d) (i : G.ColorIndex) :
    HasDerivAt (fun t : ℝ => board (lotU (t • Sie x)) (u.val.1, u.val.2, i))
      (pleatsF i (G.colorMat (Exterior.linkSum (access x) 0 (ringO u.val)))) 0 := by
  rw [pieceZ]
  apply read_matrix_derivative i (runV (Sie x) 0 (ringO u.val))
  exact fun _ => (pleatsEq _ _).symm

set_option maxHeartbeats 200000 in
lemma äder (u:UsedEdges (box b))(x:Snap G d): (fderiv ℝ (LeapV H u.val) 0) x = royal u.val (Sie x):=by
  ext1 i
  rw [champ]
  change _ = risingO (Sie x) (u.val.1, u.val.2, i)
  exact ((ray_derivative H u x i).unique (holonomy_read H u x i)).trans
    ((contour_read u x i).unique (arcRead (Sie x) (u.val.1, u.val.2, i)))
end YM.OPE.Spells
