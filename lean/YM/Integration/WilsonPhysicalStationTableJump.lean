import YM.Integration.WilsonPhysicalStationFiledHead
import YM.Integration.WilsonMeasuredPublicEntranceOrderedPins

/-! The change between two nominated Wilson reporting tables on one original
cutoff and period, with its measured thermal diagonals and uncentered peer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationTableJump
open Filter Finset Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationFiledHead (tagged)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
  {D:ℕ}(A B:Vane R.family D)(d:Fin (D+1))

def table {N p:ℕ}(checked:A.checked f H D)(top:A.k<N):R.family.label d≃ₗ[ℂ]R.family.label d:=
  LinearEquiv.ofBijective (A.R N p d)
    ((((checked.rate N p top).1 d).1).bijective R.family R.makes (checked.early d) top.le (A.R N p d))

theorem stamped (w:(Bel R.family.book).Field d){N p:ℕ}(checked:A.checked f H D)(top:A.k<N):
    A.wheel.atCut (N,p) d w=(table R A d (p:=p) checked top).symm (tagged R A d w N p):=by
  apply (table R A d (p:=p) checked top).injective
  rw [LinearEquiv.apply_symm_apply]
  exact WilsonPhysicalStationFiledHead.exact_calibration R A d w checked top

def change (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N):R.family.label d:=
  B.R N p d ((table R A d (p:=p) a ha).symm (tagged R A d w N p))-tagged R B d z N p

theorem original (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N)(b:B.checked f H D)(hb:B.k<N):
    A.wheel.atCut (N,p) d w-B.wheel.atCut (N,p) d z=
      (table R B d (p:=p) b hb).symm (change R A B d w z (p:=p) a ha):=by
  apply (table R B d (p:=p) b hb).injective
  rw [LinearEquiv.apply_symm_apply,map_sub]
  change _-B.R N p d (B.wheel.atCut (N,p) d z)=_
  rw [WilsonPhysicalStationFiledHead.exact_calibration R B d z b hb,stamped R A d w a ha]
  rfl

def pair (N p j:ℕ)(o:Fin 2 → Cover)(x y:R.family.label d):ℂ:=
  WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) (fun _:Fin 2=>d.val) j o N p ![x,y]

theorem first (N p j:ℕ)(o:Fin 2 → Cover)(x x' y:R.family.label d):
    pair R d N p j o x y-pair R d N p j o x' y=pair R d N p j o (x-x') y:=by
  let M:=R.family.ensemble (N:=N) (p:=p) (fun _:Fin 2=>d.val) (fun i=>location R.family.S j N p (o i))
  have moved (u:R.family.label d):Function.update (![x,y]:Fin 2→R.family.label d) 0 u=![u,y]:=by
    funext i;fin_cases i <;>simp [Function.update]
  change M ![x,y]-M ![x',y]=M ![x-x',y]
  simpa only [moved] using (M.map_update_sub (![x,y]:Fin 2→R.family.label d) 0 x x').symm

theorem hearing (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N)(b:B.checked f H D)(hb:B.k<N)
    (j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label d):
    pair R d N p j o (A.wheel.atCut (N,p) d w) peer-pair R d N p j o (B.wheel.atCut (N,p) d z) peer=
      pair R d N p j o ((table R B d (p:=p) b hb).symm (change R A B d w z (p:=p) a ha)) peer:=by
  rw [first,original R A B d w z a ha b hb]


variable {E:ℕ}(V:Vane R.family E)(inside:d.val≤E)
private abbrev cell:Fin (E+1):=⟨d.val,Nat.lt_succ_of_le inside⟩

def nominated (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N):R.family.label d:=
  V.R N p (cell d inside) ((table R A d (p:=p) a ha).symm (tagged R A d w N p))-
    tagged R V (cell d inside) z N p

theorem mixed (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N)
    (b:V.checked f H E)(hb:V.k<N):
    A.wheel.atCut (N,p) d w-V.wheel.atCut (N,p) (cell d inside) z=
      (table R V (cell d inside) (p:=p) b hb).symm (nominated R A d V inside w z (p:=p) a ha):=by
  apply (table R V (cell d inside) (p:=p) b hb).injective
  rw [LinearEquiv.apply_symm_apply,map_sub]
  change _-V.R N p (cell d inside) (V.wheel.atCut (N,p) (cell d inside) z)=_
  rw [WilsonPhysicalStationFiledHead.exact_calibration R V (cell d inside) z b hb,stamped R A d w a ha]
  rfl

theorem mixed_hearing (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N)
    (b:V.checked f H E)(hb:V.k<N)(j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label d):
    pair R d N p j o (A.wheel.atCut (N,p) d w) peer-pair R d N p j o (V.wheel.atCut (N,p) (cell d inside) z) peer=
      pair R d N p j o ((table R V (cell d inside) (p:=p) b hb).symm (nominated R A d V inside w z (p:=p) a ha)) peer:=by
  rw [first,mixed R A d V inside w z a ha b hb]

end YM.Integration.WilsonPhysicalStationTableJump
end
