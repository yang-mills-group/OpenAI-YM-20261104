import YM.Integration.WilsonOriginalPublicNodalBufferedCellProbe
import YM.Integration.WilsonOriginalPublicNodalBufferedOrbit

/-! On the genuine planted raw group, translating an input test changes precisely its finite jet factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedCellRow
open Function Finset PowerSeries Lattice RG Wilson Tree Source Labels Precision XSpace XSpace.Cirrus
open WilsonCoeffUV.Shard
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato
open WilsonIndependentRawRosterWord (film)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedOpeningHomes (rent name site)
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentSpoutPhysicalHomes (filmAt load)
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)
  (cut:∀i,d i<D i)(Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)
  (y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→ CellR)
abbrev Frames (i:Fin (n+1)):=R.family.labels.level (d i)
abbrev Source:=(i:Fin (n+1))→Verse (Frames R d i)
abbrev Stamps:=(i:Fin (n+1))→Alma (Frames R d i)

def profile (ξ:Fin (n+1)→Point4)(i:Fin (n+1)):Rarity (D i):=
  placed (T i) (x i) y σ sp (o i) (ξ i)
def gain (ξ:Fin (n+1)→Point4)(z:Fin (n+1)→ Cover)(a:Stamps R d):ℝ:=
  ∏i,drumB (d i) (x i)*jewelBloom (cut i) (a i)
      (wheelC (x i) y (z i) (profile D T x y σ sp o ξ i).ψ (o i))
def bank (c:Source R d)(z:Fin (n+1)→ Cover)(a:Stamps R d):ℂ⟦X⟧:=
  complex (∏i,c i (a i))*
    Bare.normalized (W.tree Y.F.p) G (film R W kind d (fun i=>sheet (Frames R d i) (a i)) Y z (branch n id))

theorem constant (k:ℝ):complex (PowerSeries.C k)=PowerSeries.C (k:ℂ):=by
  unfold complex
  rw [PowerSeries.map_C]
  rfl

theorem deposit (c:Source R d)(ξ:Fin (n+1)→Point4)
    (u:WilsonIndependentSpoutPhysicalHomes.Visits R d D (fun _:Unit=>profile D T x y σ sp o ξ)
      (fun _=>x) (fun _=>y) (fun _=>o) ()):
    let z:=fun i=>(u i).1.val
    let a:=fun i=>(u i).2
    load R d D cut (fun _:Unit=>profile D T x y σ sp o ξ) (fun _=>x) (fun _=>y)
      (fun _=>o) () c (fun _=>1) u=
    PowerSeries.C (gain R d D cut T x y σ sp o ξ z a)*∏i,c i (a i):=by
  intro z a
  let φ:=profile D T x y σ sp o ξ
  let k:=fun i=>drumB (d i) (x i)*jewelBloom (cut i) (a i) (wheelC (x i) y (z i) (φ i).ψ (o i))
  have slot (i):
      rent R d D cut c φ x y o (fun _=>1) d i (u i)=PowerSeries.C (k i)*c i (a i):=by
    unfold rent realDose k
    rw [one_smul,map_mul]
    ring
  have wage:load R d D cut (fun _:Unit=>φ) (fun _=>x) (fun _=>y) (fun _=>o) () c (fun _=>1) u=
      PowerSeries.C (∏i,k i)*∏i,c i (a i):=by
    unfold load
    simp only [slot,prod_mul_distrib,map_prod]
  exact wage

theorem original (c:Source R d)(ξ:Fin (n+1)→Point4)
    (u:WilsonIndependentSpoutPhysicalHomes.Visits R d D (fun _:Unit=>profile D T x y σ sp o ξ)
      (fun _=>x) (fun _=>y) (fun _=>o) ()):
    let z:=fun i=>(u i).1.val
    let a:=fun i=>(u i).2
    complex (load R d D cut (fun _:Unit=>profile D T x y σ sp o ξ) (fun _=>x) (fun _=>y)
      (fun _=>o) () c (fun _=>1) u)*
      filmAt R W kind d D (fun _:Unit=>profile D T x y σ sp o ξ) (fun _=>x) (fun _=>y)
        (fun _=>o) (fun _=>Y) () u=
      PowerSeries.C (gain R d D cut T x y σ sp o ξ z a:ℂ)*bank R W kind d Y c z a:=by
  intro z a
  rw [deposit,map_mul,constant]
  exact mul_assoc _ _ _

theorem continuous_row (c:Source R d)(z:Fin (n+1)→ Cover)(a:Stamps R d)(q:ℕ):
    Continuous fun ξ:Fin (n+1)→Point4=>PowerSeries.coeff q
      (PowerSeries.C (gain R d D cut T x y σ sp o ξ z a:ℂ)*bank R W kind d Y c z a):=by
  simp only [coeff_C_mul]
  exact (Complex.continuous_ofReal.comp
    (WilsonOriginalPublicNodalBufferedCellProbe.product cut T x y σ sp o z a)).mul continuous_const

end YM.Integration.WilsonOriginalPublicNodalBufferedCellRow
end
