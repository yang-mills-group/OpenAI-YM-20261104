import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Piccolo

/-! A supported real insertion at any honest original root. Every derivative uses
the same tag and fine scalar in the joint chart, including winding supports. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactHymn
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

-- no Short prerequisite
theorem original (h : Panes S V x X P n C g) (hw : u*‖tape w‖ ≤ loom P (reach x) C) (hW : Healthy B.threshold X (a.received k T q d u V U w)) :
    let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ grandFee Q' * (ample n X P B Q M C x)^n * τ := by
  intro f₀
  let z := a.overture T k V g w u D; let f := f' ∘ increment (a.received k T q d u V U w)
  have hw (g) := (a.extra_size g u hu w).trans hw
  obtain ⟨hz,hz'⟩ := a.reprise hT h h' origin hQ hC hM hn hl ht ht' hpow hs hr.le hw hd
  have h0 : z 0=0 := by unfold z Museum.overture; rw [Sample.journey_origin,a.overt_home]
  have hf : ContDiffAt ℝ n f (z 0) := h0.symm ▸ (regular.smooth _ hW).of_le (Nat.cast_le.mpr hB)
  have HH := a.overt_at (q:=q) (d:=d) hT b h U hC hr hw (W:=fun _ => w) (flowJourney V D) ?ready
  case ready =>
    intro i hi
    let L y := a.pane V u w (g i) i (journey V l D y) w
    have hL : ContDiffAt ℝ n L 0 := (((h.fits i hi).ready D).prodMk contDiffAt_const).prodMk contDiffAt_const
    have he : L 0=a.pane V u w (g i) i V w := by unfold L; rw [Sample.journey_origin]
    exact he ▸ hL.continuousAt.tendsto
  have heq : f₀ ∘ journey V l D =ᶠ[𝓝 0] f ∘ z := HH.mono fun _ hv => regular.sites _ _ hv
  refine ⟨(hf.comp _ hz).congr_of_eventuallyEq heq,fun j hj => ?_⟩
  rw [(heq.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]; let A := ample n X P B Q M C x; have hA : 1 ≤ A := ample_one n X P B hQ hM hC
  have ht := hE.1; have hQ := Q'.large
  rw [grandFee,show ample n X P B Q M C x=A from rfl,show (patterns n*Q'.fee)*A^n*τ=patterns n*(A^n*Q'.fee*τ) by ring]
  refine slots_bound hz hf hj (by positivity : 0≤A^n*Q'.fee*τ) (fun p v hv => ?_); rw [h0]
  refine (Q'.born _ _ (fun _ => A) (p.length_le.trans hj) ((p.length_le.trans hj).trans hB) regular hE hW
    (fun i => hz' _ (p.partSize_pos i) ((p.partSize_le i).trans hj) _ (fun _ => hv _))).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; gcongr; exact p.length_le.trans hj


end YM.Integration.WilsonLongContactHymn
