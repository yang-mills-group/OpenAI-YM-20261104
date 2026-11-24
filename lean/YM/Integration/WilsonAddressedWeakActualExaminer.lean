import YM.Integration.WilsonAddressedWeakPostedCylinder
import YM.Integration.WilsonAddressedWeakSoftTerminal
import YM.MergeProof.West.Equity

/-! Read the actual displaced group fields against their own filed Wick polynomials on the
same protected physical stock, including each lower face of the reflected product. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedWeakActualExaminer
open Function Set Filter Lattice Wilson RG MeasureTheory Marker Cells Next.Rank
open Next.Rank.Perch Next.Rank.Atlas Next.Rank.Rise Next.Rank.Normal Next.Rank.Ribbon Next.Rank.Spindle
open Next.Rank.Glyph Next.Rank.Exponential Next.Rank.Camp Next.Rank.Peak Next.Rank.Station Next.Rank.Value
open Next.Rank.Tapes Next.Rank.Tapes.West Next.Rank.Dock Next.Rank.Read Next.Rank.Ship
open PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {k N p n m:ℕ} {ξ:Purse} {c:Course C N p k}
variable {P:(i:ℕ)→Rep G (C.side i p)} {Ψ:AtlasData G C.S p} {R:Lead G C.S p}
variable {x:Points n} (fit:Fit (C.path.levels) ξ.band k x) (B:Fin n→(standard C).Tag)
variable (raw:Config G (C.side N p)→veil (Fin n)) (V:Fin n→poly (Chamber G C.S k p))
variable (chast:Chast P c Ψ x V ξ m (Array.stamp (Ship.yard C ξ.band c.allow p) (C.beta N p) raw))
variable (Wick:∀ y:Chamber G C.S (middle (C.path.levels) ξ.band k) p→ℝ, Next.Rank.Atlas.Wind (C.path.levels) y (fraction n ξ.taylor (clim (C.path.levels) k)) →
    ‖t_cum (track Ψ) V (before (C.path.levels) ξ.band k) y-(Ship.targets C B fit)‖+Perch.bill (-3/2) (clim (C.path.levels) k)≤Perch.bill (-31/32) (clim (C.path.levels) k))
variable (route:Peak.sufficiently C B ξ.band x k) (hn : n ≤ m)

include chast Wick hn route

theorem posted (g:(P (middle (C.path.levels) ξ.band k)).p.B=Perch.walls (clim (C.path.levels) (middle (C.path.levels) ξ.band k))) (hs:Perch.Shelf ξ.era.coast m (clim (C.path.levels) k) (clim (C.path.levels) (middle (C.path.levels) ξ.band k))) :
    WilsonAddressedWeakPostedCylinder.middlePost (Peak.Meter (C.path.levels) g hs) ξ.era.coast.Q c c.allow raw B fit := by
  obtain ⟨ι,κ,hi,hk,H,K,W,fees,bg,push,addresses,healthy⟩:=chast g hs
  refine ⟨ι,κ,hi,hk,H,K,W,?_,fees,bg,push⟩
  apply Peak.warming hs g hn (fun i=>(addresses i).2) (fun i=>(addresses i).1) _ (route fit p N c.allow)
  intro i U hU
  obtain ⟨y,hy,seen⟩:=healthy i.1 U hU
  let Q:=t_cum (track Ψ) V (before (C.path.levels) ξ.band k) y
  let v:=(W i).value U
  let z:=Peak.view (Ship.yard C ξ.band c.allow p) (Ship.targets C B fit) i
  let a:=(Array.reorient (Ship.yard C ξ.band c.allow p) i.1 Q).part i.2.val
  have ha:‖a+z‖≤‖Q-(Ship.targets C B fit)‖:=Next.Rank.Atlas.honor (C:=C) (T:=Ship.yard C ξ.band c.allow p) i.1 Q (Ship.targets C B fit) i.2
  have hv:‖v-a‖≤Perch.bill (-3/2) (clim (C.path.levels) k):=seen i.2
  change ‖v+z‖≤_
  rw [show v+z=(a+z)+(v-a) by ring]
  exact (norm_add_le ..).trans ((add_le_add ha hv).trans (Wick y hy))

/-- The comparison datum is the explicit finite Gaussian polynomial in the middle chamber.
The terminal estimate is for the unchanged, integrated compensated physical cylinder. -/
theorem original (O:HaarBudget G) (charge:Peak.Charge (C.path.levels) ξ.band k m O ξ.era)
    (bank:Ship.bank O (C.path.levels) (width (C.path.levels) ξ.band k)) (market:Nylon c P Ψ R ξ)
    (crew:Plessey ξ x c P R m) (continuous:∀ i:modes (Fin n),Continuous fun U=>(raw U).part i)
    (S:modes (Fin n)) (occ:S.val.Nonempty) :
    (Ship.yard C ξ.band c.allow p).rootTest (C.beta N p) (fun U=>(Poly.pass (-(Ship.targets C B fit))*raw U).part S) ≤ Ship.budget (C.path.levels) m k := by
  let Y:Config G (C.side N p)→veil (Fin n):=fun U=>Poly.pass (-(Ship.targets C B fit))*raw U
  have hc:=market.use_ (middle (C.path.levels) ξ.band k) (wider ..) (before (C.path.levels) ξ.band k)
  have hs:=charge.tally.stops _ (charge.assured _ (wider ..) le_rfl)
  let J:=Peak.Meter (C.path.levels) hc.budget hs
  have receipt:=posted fit B raw V chast Wick route hn hc.budget hs
  have hm:=WilsonAddressedWeakPostedCylinder.posted J ξ.era.coast.Q c c.allow raw continuous B fit
    charge.allot.permitted hn receipt (hc.budget ▸ hs.span) (hc.budget ▸ hs.space)
  have he:spouse (clim (C.path.levels) k) ξ.era ((middle (C.path.levels) ξ.band k)-(middle (C.path.levels) ξ.band k))=J.output:=by dsimp only [spouse];rw [Nat.sub_self,pow_zero,one_mul];rfl
  have paid:Ship.estimate (P (width (C.path.levels) ξ.band k)) c c.allow x Y ξ.era.coast.e 1 1 (Ship.allowance (C.path.levels) m k):=by
    apply Perch.covers c P ξ.band x m c.allow (turns_X charge.allot.permitted charge.tally crew Y)
      charge.allot.permitted charge.tally charge.assured
    apply Perch.follows hm he.symm.le
    exact hs.reserve.trans_eq (congr_arg (·*Perch.w (clim (C.path.levels) (middle (C.path.levels) ξ.band k))) he.symm)
  apply WilsonAddressedWeakSoftTerminal.whole O charge.allot bank
    (market.use_ _ le_rfl ((wider ..).trans (before (C.path.levels) ξ.band k))).chand Y _ hn ξ.era.coast.base le_rfl le_rfl paid S occ
  intro i
  simp only [Y,Glyph.part_mul]
  exact continuous_finsetSum _ fun j _=>continuous_const.mul (continuous _)

end YM.Integration.WilsonAddressedWeakActualExaminer
