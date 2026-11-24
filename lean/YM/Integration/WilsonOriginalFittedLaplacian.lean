import YM.Integration.WilsonPhysicalTestFibre

/-! The trace of the fitted grade-six test derivative, with a single real
four-dimensional test and the actual full ordinary field on the K-torus. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalFittedLaplacian
open Finset Set Function Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonPhysicalTestFibre (Slice chart line)
open WilsonPhysicalReturnedTestDirection (value)
open LocalLTE.Weft WilsonPosteriorProjectionStencil WilsonSmoothUnitFiniteGrid
open WilsonSmoothUnitLatticeDifference (coef)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(d:Fin 3 → ℕ){N per f K requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
variable (station:A.slot=file.station)(axes:A.axis=file.A N per)
variable (s:(Stock.census (Fin 3)).Mode)(sites:Fin 3 → Site (R.family.side K per))(slot:Fin 3)
  {b:ℕ}(stop:b≤K)(W:Config G (R.family.side b per))

def difference {n:Side}(k:ℕ)(j:J k)(left:Axis → ℝ)(h:ℝ)(φ:Four ℝ → ℝ)
    (F:(a:Axis) → Slice n a → Per n → ℂ)(a:Axis)(x:Site n):ℂ:=
  let yt:=(chart n a).symm x
  let u:=point (left a) h yt.2
  let t:=(width k:ℝ)*h
  let ψ:=line φ left h a yt.1
  ((coef ψ u j.val*t^j.val:ℝ):ℂ)*F a yt.1 yt.2-
    (ψ u:ℂ)*∑i:J k,(weight k i j:ℂ)*F a yt.1 (yt.2-(offset i:Per n))

include station axes in
theorem original (k:ℕ)(hk:1≤k)(left:Axis → ℝ)(ρ:ℝ)(rp:0<ρ)
    (fit:width k≤(R.family.side K per).val)(φ:Four ℝ → ℝ)
    (mass:Axis → Site (R.family.side K per) → ℝ)(nonneg:∀a x,0 ≤ mass a x)
    (regular:∀a (y:Slice (R.family.side K per) a),
      ContDiff ℝ (↑(2*k+1):WithTop ℕ∞) (line φ left (R.family.S.a K/ρ) a y))
    (clear:∀a (y:Slice (R.family.side K per) a) z,
      z≤left a+(width k:ℝ)*(R.family.S.a K/ρ) ∨ left a+((R.family.side K per).val:ℝ)*(R.family.S.a K/ρ)≤z →
      line φ left (R.family.S.a K/ρ) a y z=0)
    (heads:∀a (y:Slice (R.family.side K per) a) (x:Per (R.family.side K per)) z,
      let h:=R.family.S.a K/ρ
      z∈Icc (point (left a) h x) (point (left a) h x+(width k:ℝ)*h) →
      ‖iteratedDeriv (2*k+1) (line φ left h a y) z‖ ≤ mass a (chart (R.family.side K per) a (y,x))):
    let n:=R.family.side K per
    let h:=R.family.S.a K/ρ
    let j:J k:=⟨2,by omega⟩
    let F:=fun (a:Axis)(y:Slice n a)(z:Per n)=>
      value R d A file s (Function.update sites slot y.val) slot a stop W z
    let M:=∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K)^power)
    ‖∑x:Site n,∑a:Axis,difference k j left h φ F a x‖≤
      ∑a:Axis,∑y:Slice n a,cost k j*((width k:ℝ)*h)^(2*k+1)*(∑z:Per n,mass a (chart n a (y,z)))*M:=by
  let n:=R.family.side K per
  let h:=R.family.S.a K/ρ
  let j:J k:=⟨2,by omega⟩
  let F:=fun (a:Axis)(y:Slice n a)(z:Per n)=>
    value R d A file s (Function.update sites slot y.val) slot a stop W z
  apply WilsonPhysicalTestFibre.total
  intro a y
  have hor:=WilsonPhysicalReturnedTestDirection.original R d A file station axes s
    (Function.update sites slot y.val) slot a stop W k j (left a) ρ rp fit (line φ left h a y)
    (regular a y) (clear a y) (fun z:Per n=>mass a (chart n a (y,z))) (fun z=>nonneg a _) (heads a y)
  simpa only [difference,Equiv.symm_apply_apply,Finset.sum_sub_distrib] using hor
end YM.Integration.WilsonOriginalFittedLaplacian
