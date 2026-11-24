import YM.Extra.WEAK_SCALING_ACTLAW.Orientation
import YM.OPE.Coverage.Store
/-!
## Keep the actual stress normalization data when applying the weak orientation
and flux transport procedure already at finite demands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Curve
open Function Set Filter Table Ward Spec Org Climb
open scoped Topology ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {V : DiffPlan S} {T : Lighthouse C.book}
variable {h : S.RealSpin} {H : (Free C).RealSpin} {M D N m d : ℕ} {Q R : ℝ} (b : Curve V T.W h H M D Q)
theorem tracks_cal (hr : 1 ≤ R) (hQ : R < Q) (hn : N ≤ M) (hd : d + m < D) (h₄ : 4 < D)
    (hS : S.Hierarchy) (hV : V.Derivatives S) (hH : (Free C).Hierarchy) (hW : T.W.Derivatives (Free C))
    {J : S.Stress} (hJ : J ≠ 0) {σ : ℕ → ℕ} (hs : Tendsto σ atTop atTop) {c : ℝ}
    (hpos : 0 < c) (he : Tendsto (b.micro J ∘ σ) atTop (𝓝 (c • T.J))) {p : ℝ → Prop} (hpass:∀ᶠ k in atTop, p (c * ‖b.pull J (σ k)‖*b.r (σ k)^4)) :
    ∃ X, Track X V T J h H N d m R ∧ (∀ᶠ i in atTop,p (X.xi i)) := by
  obtain ⟨u,hu,ha,hp⟩ := downwards (hs.eventually b.graded) (fun i => b.pos (σ i)) (b.shrinks.comp hs)
  let s := σ ∘ u
  have ht : Tendsto s atTop atTop := hs.comp hu.tendsto_atTop
  let t k := b.r (s k)
  have hw k := b.pull_norm hJ k
  let X : Scaling S := ⟨b.X ∘ s, fun k => c*‖b.pull J (s k)‖*(t k)^4,t,fun k => by
      have hr := b.pos (s k); have := hw (s k); dsimp only [t]; positivity, fun k => b.pos _,ha,b.shrinks.comp ht⟩
  refine ⟨X,⟨⟨fun k e hb => ⟨((hp k).1 e (by omega)).1,((hp k).1 e (by omega)).2.1⟩,
    fun k e hb => ((hp k).1 e (by omega)).2.2,fun k i e h h' v => (hp k).2 i e h (by omega) v⟩,
    fun n hy j hj v hv ε hε => ht.eventually (b.tested hS hV hH hW hr hQ (hy.trans hn) v hv j (by omega) ε hε),
    fun i j => ?_⟩,?_⟩
  swap; · exact hu.tendsto_atTop.eventually hpass
  have converges_on {j : ℕ → (Free C).Stress} {z} (h : Tendsto j atTop (𝓝 z)) (a c : Axis) :
    Tendsto (fun k => j k a c) atTop (𝓝 (z a c)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) c
  have hi := (converges_on (he.comp hu.tendsto_atTop) i j).const_smul (c⁻¹ : ℝ)
  change Tendsto _ _ (𝓝 ((c⁻¹:ℝ) • c • T.J i j)) at hi
  rw [inv_smul_smul₀ hpos.ne'] at hi
  apply hi.congr
  intro k
  change (c⁻¹:ℝ) • b.micro J (s k) i j = (b.X (s k) 4).symm ((↑((_ : ℝ) * (t k)^4) : ℂ) • J i j)
  have hr : t k ≠ 0 := (b.pos _).ne'
  rw [map_smul,show (c*‖b.pull J (s k)‖*t k^4)⁻¹*t k^4 = c⁻¹*‖b.pull J (s k)‖⁻¹ by field_simp]
  exact (mul_smul (c⁻¹:ℝ) ‖b.pull J (s k)‖⁻¹ _).symm.trans (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _)


end YM.Extra.WeakScaling.Curve
namespace YM.OPE.Coverage
open Function Set Filter Extraction Climb Ward Table Org Maxwell Spec Next.UVStress Extra
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open WeakScaling
variable {G : Gauge}{C:Family G}{S:Table C.book}{F:Order}{V:DiffPlan S}{T:Lighthouse C.book}{h':Extraction.Order}
set_option quotPrecheck false
local notation "T₀" => Bel C.book

-- free line normalization bridge at arbitrary MaxwellData meeting FreeDiv
lemma charge_line {Q:MaxwellData C} (h : FreeDiv Q.T Q.hT Q.lit.hers) : Line Q.T Q.hT.spin:=by
  intro P hQ hR hC
  have ready (X:(T₀).Stress) (hX:Conserved Q.T.W Q.hT.spin X)(hY:RawTensor Q.hT.spin X)(hZ:Centered X) : X∈ KernelSpace Q.hT.spin:=by
     refine kernel_mem.mpr ⟨sym_mem.mpr ⟨hX.symmetric,hX.real,hY⟩,?_⟩
     intro a b; have h₁ := hZ a b
     rw [Work.A15.front_apply] at h₁
     change Work.A01.frontRead _ _ _ _=_; rw [Work.A01.front_eval]
     convert h₁ using 1 -- Fin 0 defs
     apply congrArg _; exact congrArg (Fin.cons _) (Subsingleton.elim ..)
  let b:KernelSpace Q.hT.spin:=⟨Q.T.J,h.enters⟩
  let u : LinearMap.ker (currentDiv Q.T.W Q.hT.spin Q.lit.hers) := ⟨b,(linear_cons ..).2 h.origin⟩
  let p:KernelSpace Q.hT.spin:=⟨P,ready _ hQ hR hC⟩
  let v:LinearMap.ker (currentDiv Q.T.W Q.hT.spin Q.lit.hers):=⟨p,(linear_cons ..).2 hQ⟩
  have hw : u ≠ 0:=fun H=> h.sign (congr_arg (fun (x : LinearMap.ker (currentDiv Q.T.W Q.hT.spin Q.lit.hers)) => x.val.val) H)
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' u hw).mp h.one v
  exact ⟨c, (congr_arg (fun (x : LinearMap.ker (currentDiv Q.T.W Q.hT.spin Q.lit.hers)) => x.val.val) hc).symm⟩
end YM.OPE.Coverage
