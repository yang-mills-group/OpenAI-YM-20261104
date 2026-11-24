import YM.Integration.WilsonPointChildEra
import YM.Integration.WilsonPointChildCoveredRead
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildFoldedField
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{α:Type}{D d r:ℕ}{o:Loc G 1}

/-- The source and target periodization retain exactly the same lifted
arguments, including the rank-zero charged scalar. -/
theorem folded (Z:Tile (Biglot α) r)(n:Side):sieve n Z=Bank.Carp.plume Z n:=by
  funext x
  rw [sieve_i, Bank.Carp.plume]
  rfl

def field (d:ℕ)(Y:Anthem D G)(p:Studio D):Era G ℝ:=
  (fun n=>rancho (Kemp.banner d (Y p) n),Y p)

theorem print {Y:Anthem D G}(h:Clef o Y d)(p:Studio D)(n:Side)(e r:ℕ):
    (field d Y p).1 n e r=Bank.Carp.plume ((Y p) e r) n:=
  (badge (Y p) (h.fare.1 p) (fun e r=>h.fare.2.1 p e r) le_rfl ..).trans (folded _ n)

theorem original {Y:Anthem D G}(h:Clef o Y d)(p:Studio D):Auth d (field d Y p):=by
  have rank(n:Side):shellK d ((field d Y p).1 n):=by
    intro e r large
    rw [print h p n e r]
    have vanish:(Y p) e r=0:=by
      by_contra hn
      exact (not_le_of_gt large) (h.fare.1 p e r hn)
    rw [vanish,Bank.Carp.plume_zero]
  refine ⟨?_,rank,?_,?_⟩
  · intro e r
    obtain ⟨s,A,hs,_,paid⟩:=h.fare.2.2 e r
    have w:=WilsonPointChildCoveredTariff.tested (fun _:Unit=>0) () o hs.le (paid p)
    exact (Bank.Carp.caisson (w.to_cork hs.le (Finset.mem_singleton_self ())) hs).congr
      (Eventually.of_forall fun n=>(print h p n e r).symm)
  · intro n e r s x
    change rancho (Kemp.banner d (Y p) n) e r (x ∘ s)=rancho (Kemp.banner d (Y p) n) e r x
    exact Lava.marble_agate r _ x s
  · intro n
    apply certify (k:=d) (fun _:Unit=>LinearMap.id)
      (fun x y equal=>equal ()) _ (rank n)
    intro t
    have actual:rollTest (Kemp.banner d (Y p) n) (Kemp.banner d (Y p) n) 1 0:=
      WilsonPointChildEra.nonlinear ((solo_iff ..).mp h.ward n p)
    change rollTest (flash ((field d Y p).1 n)) (flash ((field d Y p).1 n)) 1 0
    rw [show flash ((field d Y p).1 n)=_ from WilsonPointChildFiniteWard.recorded _]
    exact @actual

theorem paired {Y:Anthem D G}(h:Clef o Y d)(p:Studio D)(n:Side)(e r:ℕ){s A:ℝ}(hs:0<s)
    (bought:Knoxville (fame _) s (0,o) (Y p e r) A):
    MarkU (fun _:Unit=>0) {()} ((field d Y p).1 n e r) ((field d Y p).2 e r) (s/32)
      ((priceM (Loc G 1) r s + tiePay (Loc G 1) r (s/4) + 1)*A):=by
  rw [print h p n e r]
  exact plumeW (WilsonPointChildCoveredTariff.tested _ () o hs.le bought) (Finset.singleton_nonempty ()) hs

end YM.Integration.WilsonPointChildFoldedField
