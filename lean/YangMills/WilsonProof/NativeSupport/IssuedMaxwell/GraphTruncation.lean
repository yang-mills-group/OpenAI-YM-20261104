import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphAntidiagonal
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphSpectator
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphFirstPort
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphTruncation
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.O.Project
open YM.FVA2.Scale YM.FVA2.Scale.Equator PowerSeries
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

abbrev album:=install (wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core))
theorem original (u:Scan g.core n)(v:Scan g.core m)(p:FLog g.core n)(h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    coeff k (Lamp (album g) h y v (pack u t (p t x)))=
      Ordinary.truncation (B g) (read g) (GraphPrices.entered g p) (totalG u) h k (labels g v) t x y:=by
  rw [GraphAntidiagonal.original,Ordinary.truncation]
  refine Finset.sum_congr rfl fun w _=>?_
  refine Finset.sum_congr rfl fun j _=>?_
  rw [GraphFirstPort.price]
  congr 1
  refine Finset.sum_congr rfl fun i _=>?_
  rw [GraphSpectator.original]

theorem submitted (u:Scan g.core n)(v:Scan g.core m)(p:FLog g.core n)(h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    coeff k (Submit (album g) u v t p h x y)=
      read g (n+m) k (Fin.append (labels g u) (labels g v)) (forest (squeeze t x) y)-
      Ordinary.truncation (B g) (read g) (GraphPrices.entered g p) (totalG u) h k (labels g v) t x y:=by
  rw [Submit,Basket,map_sub,QuoteP,original]
  congr 1
  change coeff k (install _ _ (forest (squeeze t x) y) (Fin.append u v))=_
  rw [←GraphCorrelation.original,GraphSpectator.joined]
end IssuedMaxwell.GraphTruncation
end
