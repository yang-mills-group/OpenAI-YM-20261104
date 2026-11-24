import YM.MergeProof.Summit
import YM.UVExt.DeliveredK
import YM.UVExt.VacuumCompact
import YM.UVExt.WilsonAnalytic

/-!
Public base-stage UV interface: full-sequence statement on the periodic quadratic *linear*
kernels, finite-cutoff analytic bare-integral lemmas (not yet tuning dependence), and one
retained common UV **subsequence** for compactness of normalized evaluated vacuum densities
and effective betas. Extends the data of `Spec.Final` on the same family by true consequences,
not changing its Wilson law. Strong labelled convergence/analytic tuning/full-sequence physical
convergence are **not** contained; see UV extension report. Subsequent modules may strengthen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open RG RG.Shoot Precision RG.Supply Input Extraction Wilson Lattice Filter Function Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge}
lemma beta_subsequence (C : Family G) (h : C.path.Selected) (s : Extraction.Sequence) :
    ∃ t : Extraction.Sequence, ∃ b : ℕ→ℕ→ℝ, ∀ m p,
     Tendsto (fun j => C.path.β (s.after t j) p m) atTop (𝓝 (b m p)) := by
  obtain ⟨t,v,ht⟩ := simultaneous (ι:=ℕ×ℕ) (fun x j=> C.path.β (s j) x.2 x.1) (K:=fun x => band C.path.levels x.1)
    (fun _ => isCompact_Icc) (fun x=> (s.cofinal.eventually (eventually_ge_atTop x.1)).mono (fun i hi => (h.represents _ _ _ hi).band))
  exact ⟨t,fun m p=>v (m,p),fun m p=> (ht (m,p)).2⟩

def pricedK (C : Family G) : Prop :=
    ∃ (S : Supply.Sheet G) (D : Rolls S) (Θ : Protection D) (W : Delays Θ) (q : Bar W)
       (I : Wait q) (Z : ChartRatio G) (P : MapPrices) (L : PostCost D) (B : Directed G I Z P L) (F : ℕ → ∀ p, Shoot.Trail B.a p),
     C.path=B.bake.make F ∧ B.bake.Stays F ∧ (∀ N m p,m<N → B.Move N m p (F N p m) (F N p (m+1))) ∧ ∀ m p,
       Tendsto (fun N=>Precision.K ((B.M.H N m).metric.acts (B.a.S.side m p))) atTop
        (𝓝 (Precision.K ((YM.Next.Free.UV.stockInf B.a m (B.a.S.side m p) B.a.clock.kernel.penalty).map Complex.re))) -- `.S` agrees by the path equality.

structure Facts (C : Family G) (f : Extraction.Order) : Prop where
  linearK : pricedK C
  compactness : ∃ L : (m p : ℕ) → Config G (C.S.side m p) → ℝ,
     ∃ b : ℕ → ℕ → ℝ, ∀ m p, TendstoUniformly (fun k=>vacuum C.path (f.mesh k) m p) (L m p) atTop ∧
                    Tendsto (fun k=>C.path.β (f.mesh k) p m) atTop (𝓝 (b m p))
  finiteAnalytic : ∀ N p r (v : Fin r → C.book.Token) x,
    ∃ M : ℂ→ℂ, (AnalyticAt ℂ M (C.beta N p)) ∧ M (C.beta N p) = C.numeric N p v x ∧
       (∀ β : ℝ, M β = moment β (fun U=>∏ i, C.seen (v i) (x i) U))

lemma facts_attached {C : Family G} {f : Extraction.Order} {T : Table C.book} (H : Spec.Final C f T) :
    ∃ g : Extraction.Order, Nonempty (Spec.Final C (f.refine g) T) ∧ Facts C (f.refine g) := by
  obtain ⟨S',D,θ,W,q,I,O,K,P,B,F,hST,hPath,hmove⟩ := H.calibration
  have hx m p := horizon_limit B.M B.plan m p; have hw := H.room.cutoff.wilson
  obtain ⟨t₁,L,h⟩ := vacuum_subsequence hw f.mesh
  obtain ⟨t₂,b,hb⟩ := beta_subsequence C hw (f.mesh.after t₁)
  let g : Extraction.Order := ⟨t₁.after t₂,.full⟩
  refine ⟨g,⟨H.onward g⟩,⟨S',D,θ,W,q,I,O,K,P,B,F,hPath,hST,hmove,hx⟩,⟨L,b,fun m p=> ⟨fun V hV =>
     t₂.cofinal.eventually (h m p V hV),hb m p⟩⟩,fun N p r v x => ?_⟩
  let φ (U : Config G (C.side N p)) := ∏ i, C.seen (v i) (x i) U
  have hφ : Continuous φ := continuous_finsetProd _ fun i _ => C.continuousO N p (v i).1 (v i).2 (x i)
  exact ⟨complexMoment φ,elementary_analytic hφ (C.beta N p) (Metric.mem_ball_self (elementaryRadius_pos _)),moment_eq_real hφ,fun _ => moment_eq_real hφ ⟩

theorem attached_start (G : Gauge) (hg : G.Simple) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book),
    Nonempty (Spec.Final C f T) ∧ Facts C f := by
  obtain ⟨C,f,T,H⟩ := MergeProof.Acme.summit G hg
  obtain ⟨g,h⟩ := facts_attached H.some
  exact ⟨C,_,T,h⟩
end YM.UVExt
