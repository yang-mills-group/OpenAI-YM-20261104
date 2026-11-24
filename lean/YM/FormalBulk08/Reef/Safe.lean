import YM.FormalBulk08.Reef.Dinner

/-! Physical finite step at arbitrary finite n (no volume theorem here).
Root-based symmetry true with full Signed; don't assume auxiliary metrics on
other horizons relate. Postulate no `(Contiguous contact)` in use. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Wick Jets Orb Matrix Filter Set Precision Work.F05 RG Wilson Lattice Tree MeasureTheory Function PowerSeries
open Stationary hiding Rays
open Laurent Bloch Next.Free Exterior Work.F08 UVExtension.Free Flat
open scoped BigOperators ContDiff Topology Classical
variable {G : Gauge} {n : Side} {K : KernelChoices} {t j : ℕ}
variable (P : Flight j t) (ρ : ChartRatio G) (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) (r : (primary P.patch K c).Choices)
    (p : Pap (wire G (c*P.patch.L))) (hp : coeff 0 p=crunch (kernelP G K.penalty P.wing _)) (hr : LocalRatio ρ) (ht : 4≤t) (hc : Civic p)
-- stronger comparison on various labels, but not Gram normalization

def tossed (Z : Pap (wire G (c*P.patch.L))) : Pap (wire G c):=flag (ferry P h L c) (flush (floor K P L c) r ρ p) (seat (floor K P L c) Z)
include hp hr ht hc
theorem landed_ward : Civic (landed P ρ h L c r p) := by
   let S:=primary P.patch K c; let H:=ferry P h L c; let F:= floor K P L c
   intro s x I inst a b k ha hb he hw hk hv hh
   obtain ⟨M,Hm⟩:= digestive F a b he hw ha hb s x k hk hv hh h ρ hr H r p hc
   have hp := consolidate P ρ h L c hr r p hp ht
   exact action_view _ _ _ _ hp hp _ _ _ _ _ Hm

theorem tossed_ward (s : Signed) (x : Site c) (Z Q : Pap (wire G _)) (hz : Rite Z Q s ((primary P.patch K c).ratio.embed x)) :
      Rite (tossed P ρ h L c r p Z) (tossed P ρ h L c r p Q) s x := by
   let H:= ferry P h L c; let F:=floor K P L c
   intro I inst a b k ha hb he hw hk hv hh
   obtain ⟨M,Hm⟩:= digestive F a b he hw ha hb s x k hk hv hh h ρ hr H r p hc
   have hp:=consolidate P ρ h L c hr r p hp ht
   refine mark_view _ _ _ _ hp hp _ _ _ _ _ Hm _ _ ?_
   rw [←lease H (motor a),healthy F a b he hw ha hb s x k hk hv Z Q hz, discount H H (motor (orbitY F s x k)) _ _]
end YM.FormalBulk08.Reef
