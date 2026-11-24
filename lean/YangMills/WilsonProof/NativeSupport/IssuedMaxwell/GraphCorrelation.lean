import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.MSOrdinaryOPE
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphCorrelation
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind
open YM.FVA2.Scale YM.FVA2.Scale.Equator YM.FVA2.Dframe
open PowerSeries
open YangMills.MSbar IssuedMaxwell.Reports
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}
abbrev sky (a:Fin n→Ordinary.Label (B g)):ℕ:=∑i,(a i).1
def stamped (a:Fin n→Ordinary.Label (B g))(i:Fin n):Sec g.core (sky g a):=
  up (Finset.single_le_sum (f:=fun i=>(a i).1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)) (a i).2
def read : Ordinary.Correlation (B g):=fun n k a x=>
  if x∈conf n then Dframe.meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)
      (sky g a) x k (stamped g a) else 0
theorem collision (k)(a:Fin n→Ordinary.Label (B g))(x:Points n)(hx:x∉conf n):read g n k a x=0:=if_neg hx
theorem regular (k)(a:Fin n→Ordinary.Label (B g))(x:Points n)(hx:x∈conf n):
    read g n k a x=Dframe.meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)
      (sky g a) x k (stamped g a):=if_pos hx

def labels (u:Scan g.core n)(i:Fin n):Ordinary.Label (B g):=⟨heft (u i),cap (u i) (le_refl _)⟩
theorem original (u:Scan g.core n)(x:Points n)(k:ℕ):
    read g n k (labels g u) x=coeff k (install (wave (Teller.logNu 1)
      (WilsonCapturedPhysicalMSDatum.original g.core)) n x u):=by
  by_cases hx:x∈conf n
  · rw [regular _ _ _ _ hx,install,dif_pos hx]
    change _=coeff k (mk _)
    rw [coeff_mk]
    rfl
  · rw [collision _ _ _ _ hx,install,dif_neg hx,map_zero]
end IssuedMaxwell.GraphCorrelation
end
