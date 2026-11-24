import YM.Integration.WilsonLongContactHymn
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata

/-! The same authenticated sector grant pays the angular response for every
old occupied origin on the full spatial support. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactHymn
section aperture
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad PhysicalNext
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {g : outfit G f c} {X : Support f} {Y : Support c} {Q M C t r x z δ N ε τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D : Slab G c l} {o : Site f} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}

variable (Q' : Rights G n) [Fintype I] (a : Museum F x A X Y I) (b : Folio.Bulletin x Pt T) (hT : Act T F x k n r Q)
    (h' : Matins T F B.power (2*C) M) (origin : o∈X) (regular : B.Regular X f') (hE : B.supBounds o X f' τ)
    (hQ : 1≤Q) (hC : 1≤C) (hM : 1≤M) (hn : 2≤n) (hl : l ≤ n) (hB : n ≤ B.order) (ht : P.threshold=temp x) (ht' : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (hs : loom P (reach x) C ≤ 1) (hr : loom P (reach x) C < r) (hd : ∀ j, P.dirBound (S.ratio.parent o) (D j)) (U : Config G f) (w : Prices G I) (hu : 0 ≤ u)
include b hT h' origin regular hE hQ hC hM hn hl hB ht ht' hpow hs hr hd hu

omit hs hr hn hC ht' in
theorem responsive (s : Seam T δ N) (hδ : 0<δ) (h₀ : 0≤N) (hL : licensed δ N S.patch.L)
    (Web : Web G) (Z : Collar G n) (hc : C=Cube.fee Z) (h : Tension Web δ Q ε x r (loom P (reach x) C) B.threshold)
    (hz : Cube.Wire P (reach x) Z) (hr : Weft G S.patch.L P B Q C x) (hn : 5≤n) (hF : 100*(1+radiusB x)≤c.val) (hV : Healthy P.threshold Y V)
    (hw : u*‖tape w‖ ≤ ε*B.threshold) :
    let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let price := grandFee Q' * (ample n X P B Q M C x)^n
    ContDiffAt ℝ n (fun z : Directions G c × Prices G I => f' (a.received k T q d u (increment V z.1) U z.2)) (0,w) ∧
      ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ price * τ := by
  subst C; intro f₀ price; obtain ⟨g,hp⟩ := framed a hV hF (by omega) hz; have hc := Cube.fee_one Z
  have hW := border_healthy s hδ h₀ hL hT hQ (by omega) h a b Z rfl hz hF ht hV U w hu hw B.threshold_pos (q:=q) (d:=d)
  have hw' := hw.trans h.noise; have hY := h.small.trans (min_le_right ..)
  refine ⟨a.joint_receives hT b hp U hc h.allows (fun g => (a.extra_size g u hu w).trans hw') regular hB hW,?_⟩
  exact original Q' a b hT h' origin regular hE hQ hc hM (by omega) hl hB ht h.coarse hpow
    ((le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw') hQ).trans hY) h.allows hd U w hu hp hw' hW

end aperture
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad PhysicalNext
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular.Foliage AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n l r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G}

section paid
variable {C : Libretto G n} {D : Record} (h : Plays C D P B Pt T x)
    (a : Museum F x A X Y ι) (origin : o∈X) (regular : B.Regular X f') (hV : Healthy P.threshold Y V)
include h origin regular hV
omit [DecidableEq ι] in
theorem prior (U : Config G f) (z : Prices G ι) (hu : 0 ≤ u) (hw : u*‖tape z‖ ≤ D.ε*B.threshold) (hτ : B.supBounds o X f' τ) :
    ContDiffAt ℝ n (fun z : Directions G c × Prices G ι => f' (a.received k T q d u (increment V z.1) U z.2)) (0,z) ∧
    ∀ l ≤ n, ∀ A : Slab G c l, (∀ j,P.dirBound (S.ratio.parent o) (A j)) →
      ‖iteratedFDeriv ℝ l (fun y => f' (a.received k T q d u (journey V l A y) U z)) 0‖ ≤ grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n * τ := by
  obtain ⟨h0,hO,hP,h₁,h₂,hL,hW,ht,hf⟩ := h.rehearsed
  have H l (hl : l ≤ n) (A : Slab G c l) (hA : ∀ j,P.dirBound (S.ratio.parent o) (A j)) := responsive (q:=q) (k:=k) (d:=d) C.rights a h.bulletin (h.acts F k) (h.stages F) origin regular hτ
    D.majorant C.matins hl hO h₁ hP hA U z hu h.sew C.width C.price hL C.web C.Z rfl ht hW hf (by have := P.order_ge; omega) h.space hV hw
  exact ⟨(H 0 (Nat.zero_le _) 0 (fun j => j.elim0)).1,fun l hl A hA => (H l hl A hA).2.2 l hl⟩

end paid
end YM.Integration.WilsonLongContactHymn
