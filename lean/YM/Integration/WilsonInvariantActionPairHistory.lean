import YM.Integration.WilsonInvariantActionPairCovariance
import YM.Integration.WilsonMacroscopicRichDescentPosterior
import YM.Next.UV_STRESS.Station

/-! The actual physical representatives occur in the original mesh-then-volume
limit. Each summand is the interacting conditional likelihood averaged against
its genuine lower Wilson law, on this same campaign and for every held depth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairHistory
open Filter Function Set Finset MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot PhysMS
open OPE OPE.Orbits OPE.Therm Next.UVStress PhysicalNext.Repeat.Legato Lattice RG Wilson
open Push.GridApprox RGComparison.Core16 Extraction Extraction.Order WilsonMacroscopicForwardTransfer
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n : ℕ} {N p u : ℕ}

def prior (T : Slices R.family.path.levels p) (h : u≤N)
    (tags : Fin n→R.family.book.Token) (x : Fin n→Site (R.family.side N p)) : ℂ :=
  ∫ V,(traversal T h).conditioned (line R.family.path p u N)
    (fun U=>∏i,R.family.seen (tags i) (x i) U) V ∂scene R.family.path N p u

theorem sum_prior (T : Slices R.family.path.levels p) (h : u≤N)
    (tags : Fin n→R.family.book.Token) (x : Fin n→Site (R.family.side N p)) :
    prior R T h tags x=R.family.numeric N p tags x := by
  let X:=fun U=>∏i,R.family.seen (tags i) (x i) U
  have usable : Integrable X (scene R.family.path N p N) := by
    rw [WilsonMacroscopicForwardTransfer.top (C:=R.family) R.makes N p]
    exact R.family.integrableR tags x
  have joint := WilsonMacroscopicForwardTransfer.joint (C:=R.family) (p:=p) R.makes h (le_refl N) X usable
    (fun _=>(1:ℂ)) (show Envelope (fun _:Config G (R.family.side u p)=>(1:ℂ)) from ⟨measurable_const,1,by simp⟩)
  simp only [backTo_const,mul_one] at joint
  simp_rw [WilsonMacroscopicRichDescentPosterior.measured R T h] at joint
  rw [WilsonMacroscopicForwardTransfer.top (C:=R.family) R.makes N p] at joint
  exact joint

def lower (cut : (N p:ℕ)→Fin (N+1)) (tags : Fin n→R.family.book.Token) (φ : Test n) (N p : ℕ) : ℂ :=
  (R.family.S.a N:ℂ)^(4*n) * ∑x:Fin n→Site (R.family.side N p),
    φ (cells R.family N p x)*prior R (someSlices R.family.path.levels p) (Nat.le_of_lt_succ (cut N p).isLt) tags x

theorem enrolled (cut : (N p:ℕ)→Fin (N+1)) (tags : Fin n→R.family.book.Token) (φ : Test n) :
    lower R cut tags φ=fun N p=>smears R.family N p tags φ := by
  funext N p
  unfold lower smears
  simp_rw [sum_prior]

variable {R} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)

def labels (y b : S.Field 4) : Fin 2→R.family.book.Token :=
  fun i=>⟨4,S.representative 4 (Fin.cons (α:=fun _:Fin 2=>S.Field 4) y (fun _=>b) i)⟩

include F in
theorem use (y b : S.Field 4) {x : Points 2} (hx : x∈conf 2) :
    S.read x (labels y b) = WilsonInvariantActionPairCovariance.slot b x y := by
  rw [WilsonInvariantActionPairCovariance.placed]
  have heq := S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 2=>4) hx
    (fun i=>S.representative 4 (Fin.cons (α:=fun _:Fin 2=>S.Field 4) y (fun _=>b) i))
  simp only [S.rep] at heq
  exact heq.symm

include F in
theorem ordered (cut : (N p:ℕ)→Fin (N+1)) (φ : Test 2) {r : ℝ} (rp : 0<r)
    (y b : S.Field 4) :
    f.limits (fun p=>suitable R.family.S p (dilate rp φ))
      (lower R cut (labels (centering S 4 y) b) (dilate rp φ))
      (WilsonInvariantActionPairCovariance.tested y b r φ) := by
  rw [enrolled]
  have source:=F.room.ordered.reads 2 (labels (centering S 4 y) b) (dilate rp φ)
  rw [zoom_integral] at source
  have ht : φ.applyTo (fun x=>S.read (r•x) (labels (centering S 4 y) b))=
      WilsonInvariantActionPairCovariance.tested y b r φ := by
    unfold WilsonInvariantActionPairCovariance.tested WilsonInvariantActionPairCovariance.covariance Test.applyTo
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x∈tsupport (φ:Points 2→ℂ)
    · rw [use F _ _ (Work.A05.smul_conf rp (φ.tsupport_subset hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]
  exact ht ▸ source

end YM.Integration.WilsonInvariantActionPairHistory
