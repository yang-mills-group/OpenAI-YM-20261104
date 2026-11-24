import YM.Integration.WilsonPositionProgramPublicFourOperator

/-! The physical deciding panel, its source stocks, and its fitted change
are selected at the radius, before the perturbative order or inversion board. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicPreframe
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East PhysicalNext.Repeat.Legato
open RG17 FullVolume Climb Next.UVStress PhysMS Maxwell XSpace XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Scale MS MS.Fleet MS.Land FVA2.Register MS.Menus Local.Physical Table.Pairing
open WilsonMatrixTicketLanesSmearedPivot WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank
open WilsonPositionProgramPublicStations WilsonPositionProgramPublicGram WilsonPositionProgramPublicMeasuredAxes
open WilsonPositionProgramPublicFiniteMatrix WilsonPositionProgramPublicPerturbation
open WilsonPositionProgramPublicOriented WilsonPositionProgramPublicFourOperator
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{f:Extraction.Order}
    {l:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{d D:ℕ}
    (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)(B:Deck G)(p:Profiles R d)
local notation "Γ" => Glyph B d

structure Frame (C r:ℝ)(cap:d≤D){s w:ℝ}(stock:Bank F l D s w) where
  horizon : ℕ
  enough : D≤horizon
  vane : Vane R.family horizon
  spin : Spin.change S d
  pair : Pair F stock cap vane enough spin r
  positive : 0<r
  checked : vane.checked f Y horizon
  radius : vane.wheel.r=r
  covers : D≤vane.k
  sizes : 0<purchaseWidth vane ∧ 20*R.family.S.a (purchaseWidth vane)<R.family.S.a (purchaseWidth vane-1) ∧
    R.family.S.a (purchaseWidth vane-1)<r*LogV r/32
  decoder : (p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d
  bounded : ‖decoder‖≤C
  reads : ∀x,decoder (samples F J Z p r x)=x
  gram : ∀x,‖x‖^2≤C^2*square (samples F J Z p r x)
  change : (ℕ×ℕ)→((Γ→ℂ)≃ₗ[ℂ](Γ→ℂ))
  observed : ∀ᶠ z in (l:Filter _),Fits F J Z B p positive pair.arm decoder z (change z)
  unique : ∀ᶠ z in (l:Filter _),Injective (coordinate B F J Z p positive pair.arm decoder true z)

theorem submitted {C r:ℝ}(cap:d≤D){s w:ℝ}(stock:Bank F l D s w)
    (order:(l:Filter _)≤f.fuse)
    (paid:WilsonPositionProgramPublicFourFrame.Paid F J Z (axes R B d) (H:=Y) p C r cap stock):
    Nonempty (Frame F J Z B p (Y:=Y) C r cap stock):=by
  obtain ⟨n,nd,W,turn,pair,hr,good,atR,high,width,L,bound,read,gram,_⟩:=paid
  let rows (i:Γ):=pair.arm true (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i)
  let M z:=measured F J Z p hr (axes R B d) (fun i=>(rows i).source) z
  have cash:=acquired L (samples F J Z p r) read M (converges F J Z p hr (axes R B d) order rows)
  let U z:=if h:∃T,Fits F J Z B p hr pair.arm L z T then h.choose else LinearEquiv.refl ℂ (Γ→ℂ)
  have paidU:∀ᶠ z in (l:Filter _),Fits F J Z B p hr pair.arm L z (U z):=by
    filter_upwards [WilsonPositionProgramPublicFittedInverse.original B F J Z p hr pair.arm L read order] with z h
    have h':∃T,Fits F J Z B p hr pair.arm L z T:=h
    simpa only [U,dif_pos h'] using h'.choose_spec
  refine ⟨⟨n,nd,W,turn,pair,hr,good,atR,high,width,L,bound,read,gram,U,paidU,?_⟩⟩
  filter_upwards [cash] with z h
  obtain ⟨V⟩:=h
  let b:=(axes R B d).equivFun
  intro x y eq
  apply b.symm.injective
  apply V.change.injective
  change b (L (M z (b.symm x)))=b (L (M z (b.symm y))) at eq
  have v (a:Γ→ℂ):V.change (b.symm a)=L (M z (b.symm a)):=LinearMap.congr_fun V.reads _
  rw [v,v];exact b.injective eq

theorem original {arch:Arch R.family}(simple:G.Simple)(bliss:Bliss F l arch Y)(lead:Leading F J)
    (income:∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F Y (J r) d)(cap:d≤D):
    ∃(T:ℕ)(p:Profiles R d)(C:ℝ),0<C ∧ ∀ᶠ r in trail,
      (let s:=WilsonThermometerUnitFilingFourPoolShell.radius arch T r
       ∃stock:Bank F l D s (dock s^T), Nonempty (Frame F J Z B p (Y:=Y) C r cap stock)) ∧
      ∀s w (stock:Bank F l D s w),Nonempty (Frame F J Z B p (Y:=Y) C r cap stock):=by
  obtain ⟨T,p,C,hC,available⟩:=WilsonPositionProgramPublicFourFrame.original F J Z (axes R B d)
    simple bliss lead income cap
  refine ⟨T,p,C,hC,?_⟩
  filter_upwards [available] with r h
  obtain ⟨s,stock⟩:=h.1
  exact ⟨⟨s,submitted F J Z B p cap s bliss.lies stock⟩,
    fun s w stock=>submitted F J Z B p cap stock bliss.lies (h.2 s w stock)⟩

end YM.Integration.WilsonPositionProgramPublicPreframe
