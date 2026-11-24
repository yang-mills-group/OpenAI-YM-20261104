import YM.Integration.WilsonThermometerSolitaryExchange
import YM.Integration.WilsonThermometerSolitaryHardPeer

/-! Real ordinary peers at their existing sites and masks, through each of the three replacements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryPeers
open Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Extra.Trajectories Next.Rank.Exponential
open WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge} {n:Side} {p:BudgetPoint} {T I I':Type} {o:Fin 3→Site n}

def join (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))(j k:Fin 3):
    Lamps T (WilsonOriginalOneColor.seats j a ⊕ WilsonOriginalOneColor.seats k b) G p o (J):=
  (WilsonOriginalOneColor.lamps j a).join (WilsonOriginalOneColor.lamps k b)

theorem one (a:Lamps T I G p o (J))(j:Fin 3)(x:T)(U:Config G n)(sa:Summable (fun i=>a.frame i x U)):
    Poly.pass ((WilsonOriginalOneColor.lamps j a).log x U)=factor j ((a.log x U).part ((J).fire j)):=by
  rw [WilsonOriginalOneColorGallery.log j a x U sa,WilsonThermometerSolitaryHardPeer.cut_shape,
    a.quiet_of_hasSum x U sa,map_zero,zero_add,pass_send (show ((J).fire j).val.Nonempty from singleton_nonempty _)];rfl

theorem two (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))(j k:Fin 3)(x:T)(U:Config G n)
    (sa:Summable (fun i=>a.frame i x U))(sb:Summable (fun i=>b.frame i x U)):
    Poly.pass ((join a b j k).log x U)=
      factor j ((a.log x U).part ((J).fire j))*factor k ((b.log x U).part ((J).fire k)):=by
  have sa':Summable (fun i=>(WilsonOriginalOneColor.lamps j a).frame i x U):=sa.subtype _
  have sb':Summable (fun i=>(WilsonOriginalOneColor.lamps k b).frame i x U):=sb.subtype _
  rw [join,Lamps.joinLog x U sa' sb',pass_add (Lamps.quiet_of_hasSum x U sa') (Lamps.quiet_of_hasSum x U sb'),
    one a j x U sa,one b k x U sb]

theorem bought (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))(j k:Fin 3)
    (w:Fin 3→ℝ)(hp:∀v,0<w v)(B:ℕ)(α:ℝ)(ea:a.Paid w B α 1)(eb:b.Paid w B α 1):
    (join a b j k).Paid (Stoop.radius w 2) B α 1:=by
  have charged:=Stoop.tighten w (join a b j k) hp (by norm_num : 1≤(2:ℝ)) (Lamps.joinPaid (WilsonOriginalOneColor.regular j a ea)
    (WilsonOriginalOneColor.regular k b eb))
  convert charged using 1; norm_num

theorem original [Countable I] [Countable I'] (a:Lamps T I G p o (J))(b:Lamps T I' G p o (J))
    (w:Fin 3→ℝ)(hp:∀v,0<w v)(B:ℕ)(α:ℝ)(apos:0≤α)(ea:a.Paid w B α 1)(eb:b.Paid w B α 1)(v:Fin 3):
    ∃ (L:Type) (_:Countable L) (E:Lamps T L G p o (J)),E.Paid (Stoop.radius w 2) B α 1 ∧
      ∀x U, Poly.pass (E.log x U)=peer (fun j=>(a.log x U).part ((J).fire j))
        (fun j=>(b.log x U).part ((J).fire j)) v:=by
  fin_cases v
  · refine ⟨_,inferInstance,join a a 1 2,bought a a 1 2 w hp B α ea ea,?_⟩
    exact fun x U=>two a a 1 2 x U (ea.sums apos hp x U) (ea.sums apos hp x U)
  · refine ⟨_,inferInstance,join b a 0 2,bought b a 0 2 w hp B α eb ea,?_⟩
    exact fun x U=>two b a 0 2 x U (eb.sums apos hp x U) (ea.sums apos hp x U)
  · refine ⟨_,inferInstance,join b b 0 1,bought b b 0 1 w hp B α eb eb,?_⟩
    exact fun x U=>two b b 0 1 x U (eb.sums apos hp x U) (eb.sums apos hp x U)

end YM.Integration.WilsonThermometerSolitaryPeers
