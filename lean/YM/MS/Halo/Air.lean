import YM.MS.Arts.Pilot
import YM.MS.Motif.Beat

set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Book
open Motif
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {F: Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
lemma vaultLeaf (P: Pilot ℂ ( SectorP n ) ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex)))(c:ℂ): P.beam (coin c)=coin c:= by
   funext l; rcases l with _|⟨i,l⟩; exact peeps _ _; rw [Pilot.met]; change _=0; apply Finset.sum_eq_zero
   intro j _; rw [show D (j,P.volp i.2) ( coin c )=0 from funext fun l=>rfl, map_zero,Pi.zero_apply,mul_zero] -- map zero apply
lemma usesLeaf (P: Pilot ℂ ( SectorP n ) ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex)))(a:Cfield G n)(w:Legs (Shore G n)) : beam P (Motif.leaf a) w= mono ( fun x: Shore G n=> P.fieldC x.1 a ) w:= by
    rcases w with _|⟨i,_|s⟩; exact peeps ..; · simp_rw [Pilot.met,peeps,at_D,Motif.leaf,node1]; simp [mul_ite,mono]
    rw [Pilot.met]; simp_rw [Motif.leaf,nodeD,vaultLeaf]; simp [coin,mono]; -- Lean coin.M.S
lemma beamMoon (P: Pilot ℂ ( SectorP n ) ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex)))(T:SectorP n→+ℂ)(w:Legs (Shore G n)): P.beam (moment T F) w = T (P.volp (net w))* P.beam F w:= by
    rw [← show ( P.beam ((T (P.volp (net w))) • F) ) w=T (P.volp (net w))* P.beam F w from (by rw [map_smul,Pi.smul_apply]; rfl)]; apply P.offset _ _ (net w) w _ rfl; intro l hl; rw [moon,hl]; rfl -- implicit args?
abbrev chair (n:ℕ)(a:Axis): Arts.L n := rises (Nat.zero_le n) a
end YM.MS.Halo
