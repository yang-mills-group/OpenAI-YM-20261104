import YM.MS.Arts.Pilot
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.OneLoop
import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Step
/-!
# Pilot for transformations on finite-component momentum planes

Dimension axes only for instances. Algebra also later color. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open scoped Topology ContDiff InnerProductSpace
variable {A B R P:Type}[Fintype A][Fintype B][CommRing R][AddCommGroup P]{p: Koszul.Sector A}{b c:Bool}
namespace Pilot
variable (K:Pilot R P p)(F H:Row A P R)
-- beam


lemma net_beam : beam K (translate F) = translate (beam K F):= by
    classical
    ext l; by_cases h:net l=0; · rw [trans_on _ _ h]; exact offset K _ _ 0 _ (by simp only [map_zero]; exact trans_on F) h
    rw [trans_off _ _ h,offset K _ 0 (net l) _ (fun i hi=> trans_off _ _ fun hv=> h ( K.volp.injective ((hi.symm.trans hv).trans (map_zero _).symm))) rfl,map_zero]; rfl
end Pilot
end YM.MS.Arts
