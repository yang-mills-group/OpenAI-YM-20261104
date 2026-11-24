import YM.Integration.WilsonSeparatedOriginalSlabWave
import YM.Integration.WilsonSeparatedOriginalPairedFolio
import YM.Integration.WilsonMixedTaggedPhysicalTest

/-! One signed finite list represents the jointly smeared, uncentered physical measurement at every admitted earlier origin. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabFolio
open Function Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Native RG05Readout.Pulse
open RG05Readout.Nuclear RG05Readout.Address RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabWave
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n N per:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))
  (o:Fin 3 → Site (R.family.side n per))(top:n ≤ N)
variable {T:Type*}(age:T → ℕ)(opened:∀a,age a+1 ≤ N)(hold:(a:T) → Config G (R.family.side (age a) per))
local notation "C"=>R.family

def allowed (r η:ℝ)(f:Fin 3 → Body):Prop:=
  buy C n per o (r*η/2) f ∧ ∀i,Tall (f i) (s i+2) 1 1

def settled (book:(Fin 3 → Body) → (T → ℂ) → Prop)(ε:ℝ)(f:Fin 3 → Body)(A:T → ℂ):Prop:=
  book f A ∧ ∀a,‖scan R s v o top (opened a) (hold a) (joint Finset.univ f)-A a‖ ≤ ε

def amount (Ψ:Wave (Fin 3))(r:ℝ)(g:Body)(a:T):ℂ:=
  ∫z in Native.box,g.val z*scan R s v o top (opened a) (hold a) (cropX Ψ o r z)

theorem original (book:(Fin 3 → Body) → (T → ℂ) → Prop){ε r η X:ℝ}(ep:0 ≤ ε)(rp:0<r)(room:r ≤ (C).S.a n)
    (sep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(cap:Tall Ψ (rank+1) 1 X)
    (sale:∀f,allowed R s o r η f → ∃A,settled R s v o top age opened hold book ε f A):
    let can:=allowed R s o r η
    let receipt:=settled R s v o top age opened hold book ε
    let quota:=earn s C n rank η r*X
    ∃L:List (Entry s can receipt),(L.map Entry.rent).sum ≤ quota ∧ ∀(g:Body)(a:T),
      ‖amount R s v o top age opened hold Ψ r g a-received g L a‖ ≤ mass g*quota*ε:=by
  intro can receipt quota
  obtain ⟨F,filed,jets⟩:=regent s («C»:=R.family) (p:=per) top o r η Ψ rp room sep small grade scatter xp cap
  have licensed:Bouquet s Native.box can F quota:=WilsonMixedTaggedPhysicalTest.relabel
    (fun _ size ok=>⟨ok,size⟩) filed
  obtain ⟨L,hL,rep⟩:=issued licensed sale
  refine ⟨L,hL,?_⟩;intro g a
  let K:=scan R s v o top (opened a) (hold a)
  have exactRead (z:E4)(hz:z∈Native.box):K (cropX Ψ o r z)=K (submitted L z):=by
    rw [rep hz];symm;apply WilsonSeparatedOriginalSlabWave.same
    exact jets z
  have exactSum:amount R s v o top age opened hold Ψ r g a=exposed g L K:=by
    trans (∫z in Native.box,g.val z*K (submitted L z))
    · apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
      exact congrArg (fun l:ℂ=>g.val z*l) (exactRead z hz)
    · exact WilsonSeparatedOriginalPairedFolio.measured g L K
  rw [exactSum]
  exact (spent g L a K (fun e _=>e.filed.2 a)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (positive g)) ep)

end YM.Integration.WilsonSeparatedOriginalSlabFolio
