import YM.TraceExtension.Prom.Front.West.Equity

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedReturn
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter Paint Vac.Numbers Prayer Glimmer Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{N n p k m u D:ℕ}{ξ:Purse}{R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s z:ℝ}{Ψ:AtlasData G C.S p}
variable {x:Points n} {d0:Fin n → ℕ} (w v:(i:Fin n)→ C.label (d0 i))

local notation "D'"=> C.path.levels
local notation "γ"=>clim C.path.levels k
local notation "b"=> ξ.band
set_option quotPrecheck false
def Signed (g : FitSky D' b k x)
    (F : (i : Fin n) → StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ) : Prop :=
  ∀ y : Chamber G C.S (middleSky D' b k) p → ℝ, Wind D' y (fraction n ξ.taylor γ) →
    ‖t_cum (track Ψ) (fun i => prefaced (F i) (v i) (Station.choose D' b k x i)) (beforeSky D' b k) y -
      Ship.targetsSky C (jointX w) g‖ + bill (-3/2) γ ≤ bill (-31/32) γ

theorem arranged (g:FitSky D' b k x)
   (F:(i:Fin n)→ StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
   (hear : Signed w v g F)
   (hp:ChastSky P c Ψ x (fun i=>prefaced (F i) (v i) (Station.choose D' b k x i)) ξ u (IssuedXSky C b x c.allow p v)):
      ArrangementsSky c.allow c P (jointX w) (q_asked (C:=C) v) g ξ.era.coast u := by
  let A0:= C.path.levels; let T:= Ship.yardSky C b c.allow p; let S := clim A0 k
  let s:= Station.choose D' b k x
  let f:= Ship.targetsSky C (jointX w) g
  intro hv hs; obtain ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,h3,h4⟩ := hp hv hs
  refine ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,fun i => ⟨(h3 i).1,(h3 i).2,fun U HH => ?_⟩⟩
  obtain ⟨y,hy,hh⟩ := h4 i.1 U HH
  let V(i):=prefaced (F i) (v i) (s i); let l:=beforeSky D' b k
  let C0:= t_cum (track Ψ) V l y
  have hz : ‖C0-f‖+bill (-3/2) S ≤ bill (-31/32) S := hear y hy
  let v:= (W i).value U; let z:= Peak.view T f i; let a:= (Array.reorient T i.1 C0).part i.2.val
  change ‖v+z‖ ≤ _
  rw [show v+z=(a+z)+(v-a) by ring]; exact (norm_add_le ..).trans ((add_le_add (honor (C:=C) i.1 _ _ i.2) (hh _)).trans hz)

open PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Market Ship
theorem original {O:HaarBudget G}(hc:ChargeSky D' b k u O ξ.era)(hZ:bank O D' (widthSky D' b k))(ht:n ≤ u)(V:NylonSky c P Ψ R ξ)(g:FitSky D' b k x)
    (target:Peak.sufficientlySky C (jointX w) b x k)(hC:PlesseySky ξ x c P R u)
   (F:(i:Fin n)→ StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
   (calibrated : Signed w v g F)
   (hp:ChastSky P c Ψ x (fun i=>prefaced (F i) (v i) (Station.choose D' b k x i)) ξ u (IssuedXSky C b x c.allow p v))
   (s : modes (Fin n)) (sh : s.val.Nonempty):
    let X:=jointX w; let Y:=q_asked (C:=C) v
    (yardSky C b c.allow p).rootTest (C.beta N p) (fun U=> (invoiceSky X Y g N p U).part s) ≤ Ship.budget D' u k:=by
   intro X Y
   have hM:Peak.InstanceSky c.allow c P ξ.era X Y g u:=⟨arranged w v g F calibrated hp,turns_XSky hc.allot.permitted hc.tally hC _⟩
   have hv:Path_Sky c P c.allow b:= fun i h hx=>V.use_ i h (hx.trans (beforeSky ..))
   have he:= v_conditionedSky c.allow c P ξ.era X Y g hc.allot.permitted hv hc.tally hc.assured hM ht target
   exact Soft.couponSky O hc.allot hZ (hv _ le_rfl (widerSky ..)|>.chand) Y X g ht ξ.era.coast.base le_rfl le_rfl he s sh

end YM.Integration.WilsonReporterWeightedReturn
