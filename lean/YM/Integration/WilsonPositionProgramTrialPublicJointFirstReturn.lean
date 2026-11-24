import YM.Integration.WilsonOriginalPublicNodalFrequencyCash
import YM.Integration.WilsonPositionProgramTrialFirstDiagram
/-! Ground and first response of the measured finite Wilson word, including the changing fitted source. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFirstReturn
open RG Lattice Wilson Tree Source Labels XSpace XSpace.Cirrus PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open PhysicalNext.Repeat.Legato WilsonIndependentRawRosterWord
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentSpoutMasterOrbitClock (measure)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOriginalPublicNodalBufferedCellRow (Stamps Source Frames gain)
open WilsonOriginalPublicNodalBufferedCellFilm (Sites Seats Disp entry paper full)
open WilsonPositionProgramTrialPublicCellHull (hull)
open scoped BigOperators Topology Classical

theorem firstCash (B:Cost)(b:constantCoeff B=1)(s:ℂ⟦X⟧)(g:ℝ):
  cash 0 g (measure B s)=coeff 0 s ∧ cash 1 g (measure B s)=coeff 0 s+(g:ℂ)*coeff 1 s:=by
  have low (j:ℕ):coeff j (measure B s)=_:=WilsonIndependentSpoutMasterOrbitClock.shares B s j
  simp [cash,low,Finset.sum_range_succ,coeff_zero_eq_constantCoeff,b]

variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)
  (cut:∀i,d i<D i)(Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)
  (y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→ CellR)

def head (c:Source R d)(a:Stamps R d):ℂ:=∏i,(constantCoeff (R:=ℝ) (c i (a i)):ℂ)
def tangent (c:Source R d)(a:Stamps R d):ℂ:=
  ∑i,(coeff (R:=ℝ) 1 (c i (a i)):ℂ)*∏j∈Finset.univ.erase i,(constantCoeff (R:=ℝ) (c j (a j)):ℂ)
def wilson (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(j:ℕ):ℂ:=
  coeff j (Bare.normalized (W.tree Y.F.p) G
    (film R W kind d (fun i=>sheet (Frames R d i) (a i)) Y z (branch n id)))

theorem formal (c:Source R d)(a:Stamps R d):
  constantCoeff (complex (∏i,c i (a i)))=head R d c a ∧
  coeff 1 (complex (∏i,c i (a i)))=tangent R d c a:=by
  constructor
  · simp only [head,complex,map_prod]; apply prod_congr rfl; intro i _; rfl
  · change (coeff (R:=ℝ) 1 (∏i,c i (a i)):ℂ)=_
    have first:=Pert.First.first_product (fun i=>c i (a i)) univ
    unfold Pert.First.first Pert.First.lead at first
    simp [first,tangent,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]

def port (H:Sites (n:=n))(c:Source R d)(ξ:Disp n)(u:Seats R d H)(j:ℕ):ℂ:=
  let z:=fun i=>(u i).1.val
  let a:=fun i=>(u i).2
  let fee:ℂ:=gain R d D cut T x y σ sp o ξ z a
  if j=0 then fee*(head R d c a*wilson R W kind d Y z a 0)
  else fee*(head R d c a*wilson R W kind d Y z a 1 + tangent R d c a*wilson R W kind d Y z a 0)

theorem rows (H:Sites (n:=n))(c:Source R d)(ξ:Disp n)(u:Seats R d H)(j:ℕ)(present:j≤1):
    coeff j (entry R W kind d D cut Y T x y σ sp o c ξ u)=port R W kind d D cut Y T x y σ sp o H c ξ u j:=by
  obtain ⟨leading,first⟩:=formal R d c (fun i=>(u i).2)
  interval_cases j
  · unfold WilsonOriginalPublicNodalBufferedCellFilm.entry WilsonOriginalPublicNodalBufferedCellRow.bank port
    rw [coeff_C_mul,coeff_zero_eq_constantCoeff,map_mul,leading]
    simp only [↓reduceIte,wilson,coeff_zero_eq_constantCoeff]
  · unfold WilsonOriginalPublicNodalBufferedCellFilm.entry WilsonOriginalPublicNodalBufferedCellRow.bank port
    rw [coeff_C_mul,coeff_one_mul,leading,first]
    simp only [Nat.reduceEqDiff,↓reduceIte,wilson,coeff_zero_eq_constantCoeff]
    ring

theorem original (c:Source R d)(xp:∀i,0<x i)(ξ:Disp n)(bounded:∀i,‖ξ i‖≤1)
    (B:Cost)(paid:constantCoeff B=1)(g:ℝ):
    let H:=fun i=>hull (T i) (x i) y σ (o i)
    let v:=fun j=>∑u:Seats R d H,port R W kind d D cut Y T x y σ sp o H c ξ u j
    let field:=paper R W kind d D cut Y T x y σ sp o c ξ
    cash 0 g (measure B field)=v 0 ∧ cash 1 g (measure B field)=v 0+(g:ℂ)*v 1:=by
  intro H v field
  have cash:=firstCash B paid field g
  have fitted (j:ℕ)(hj:j≤1):coeff j field=v j:=by
    change coeff j (WilsonOriginalPublicNodalBufferedCellFilm.paper R W kind d D cut Y T x y σ sp o c ξ)=_
    rw [WilsonOriginalPublicNodalBufferedCellFilm.original R W kind d D cut Y T x y σ sp o c xp ξ bounded]
    unfold full
    rw [map_sum]
    exact sum_congr rfl fun u _=>rows R W kind d D cut Y T x y σ sp o H c ξ u j hj
  simpa only [fitted 0 (by decide),fitted 1 le_rfl] using cash

end YM.Integration.WilsonPositionProgramTrialPublicJointFirstReturn
end
