import YM.Integration.WilsonReflectedPublicGuardedColumns
/-! A preappointed reflected physical panel with its actual occupied history and
both signed native replacements at the one common optical cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicGuardedEstate
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {order:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family order S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "lev" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

open Extra.Histories.Motion RG05Readout.Address MergeProof Push.Local
open WilsonReflectedFundedHearing WilsonReflectedFullPanel WilsonReflectedAffordableArm
def Item {N p f K d:ℕ}(q jets:ℕ)(C:ℝ)
    (Y:(C₀).label d)(fee₁:ℝ)(date:ℕ)(M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (s:Motion)(c:Site ((C₀).side f p))(V:Sight C₀ d p)(u:Emblems C₀ d)
    (est:Opened C₀ d f p)(h:f<K)(start:date≤f)(top:K≤N):Prop :=
  let y:=offer R Y est (h.le.trans top)
  let data:=reduce y
  let j:=date
        let w:=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y)
        let row:=marked R (N:=N) 0 s c V u data f
        let wage:=WilsonReflectedPublicMountedInvoice.wage R f
        let Ω:=orbitCost ((C₀).labels.level d)
        WilsonReflectedFullPanel.receipt R d j K N p jets (start.trans h.le) top (1/32) M Y
          (mesh j^d*fee₁) ∧
        ∃ A : Arm R d N p f K, A.Y=Y ∧ A.w=w ∧ A.b=s.2 ∧ A.s=s.1 ∧ A.o=c ∧
          (∃B:Arm R d N p K K, WilsonReflectedRestoredStation.Situated R h.le A B) ∧
          ∃Q E, WilsonReflectedPublicGuardedColumns.Joined R A h.le top ((charge y:ℝ):ℂ)⁻¹
            row wage (Ω*(1+wage)) ((2+Ω)*C*((β f)^q)⁻¹*fee₁) Q E

def Dossier {N p f K d:ℕ} {X:Type} (t T q jets:ℕ) (C:ℝ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)(date:Bool→ℕ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (h:f<K)(start:∀b,date b≤f)(top:K≤N):Prop :=
      ∀(I:Type) [Fintype I] [DecidableEq I] (weak:I→Bool) (v:I→X) (turn:I→Motion)
        (c:I→Site (R.family.side f p)) (names:Census I),
      (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (c i) (c j)) →
      let x:=fun i=>book (weak i) (v i)
      let y:=fun i=>offer R (x i) est (h.le.trans top)
      let data:=fun i=>reduce (y i)
      (∀i,charge (y i) ≤ max 1 (2*(β f)^((2*T+9)*(d+1))*fee₁ (weak i) (v i))) ∧
      WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn c data (fun _=>V) (fun _=>u)
        names (h.le.trans top) t ∧
      (∀i, Item (R:=R) q jets C (x i) (fee₁ (weak i) (v i)) (date (weak i)) (M (weak i))
        (turn i) (c i) V u est h (start _) top) ∧
      ∀j (hj:j ≤ N) (s:names.Mode) A,
        (WilsonThermometerReflectedRoster.density R (fun _:I=>d) (fun _=>0) turn c data
          (fun _=>u) names (h.le.trans top) hj A).part s =
        ((C₀).path.rep N p j).eval A • actualTransport C₀ (N:=N)
          (fun U=>∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p
            (WilsonReflectedPublicOrientedFaces.displayed R d (x i) (turn i))
            (((C₀).S.toDepth (h.le.trans top) p).embed (c i)) U) hj A

private def Inventory {N p f d:ℕ} {X:Type} (t T:ℕ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)(top:f≤N):Prop :=
      (∀ (weak:Bool) (v:X) (s:Motion) (c:Site (R.family.side f p)),
        let rep:=(C₀).path.rep N p f
        let data:=reduce (offer R (book weak v) est top)
        let field:=marked R (N:=N) 0 s c V u data f
        let fee₀:=WilsonReflectedPublicMountedInvoice.wage R f
        ∃q:Coefficient ((C₀).labels.level d) ((C₀).side f p),
          q.Format c (C₀).params rep ∧
          ((C₀).labels.level d).coeffSize q.x≤orbitCost ((C₀).labels.level d)*(1+fee₀) ∧
          q.remBound c rep (kappa (C₀).path f) fee₀ ∧
          field.2.1=q.exponentialEntry c ((C₀).localSection d) rep ∧
          profile rep.activities field.2.2=profile rep.activities q.forced ∧
          q.density c ((C₀).localSection d) rep=field.1) ∧
      ∀(I:Type) [Fintype I] [DecidableEq I] (weak:I→Bool) (v:I→X) (turn:I→Motion)
        (c:I→Site (R.family.side f p)) (names:Census I),
      (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (c i) (c j)) →
      let x:=fun i=>book (weak i) (v i)
      let y:=fun i=>offer R (x i) est top
      let data:=fun i=>reduce (y i)
      (∀i,charge (y i) ≤ max 1 (2*(β f)^((2*T+9)*(d+1))*fee₁ (weak i) (v i))) ∧
      WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn c data (fun _=>V) (fun _=>u)
        names top t ∧
      ∀j (hj:j ≤ N) (s:names.Mode) A,
        (WilsonThermometerReflectedRoster.density R (fun _:I=>d) (fun _=>0) turn c data
          (fun _=>u) names top hj A).part s =
        ((C₀).path.rep N p j).eval A • actualTransport C₀ (N:=N)
          (fun U=>∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p
            (WilsonReflectedPublicOrientedFaces.displayed R d (x i) (turn i))
            (((C₀).S.toDepth top p).embed (c i)) U) hj A

private def Stock {N p f K d:ℕ} {X:Type} (q jets:ℕ)(C:ℝ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)(date:Bool→ℕ)
    (M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (h:f<K)(start:∀b,date b≤f)(top:K≤N):Prop :=
  ∀ b (v : X),
      let Y := book b v
      let j := date b
      let w := (M b).symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y)
      receipt R d j K N p jets ((start b).trans h.le) top (1/32) (M b) Y (mesh j^d*fee₁ b v) ∧
      ∀ side s o, ∃ A : Arm R d N p f K, A.Y = Y ∧ A.w = w ∧ A.b = side ∧ A.s = s ∧ A.o = o ∧
        Priced R A (C*((β f)^(q+1))⁻¹*(mesh f)^d*fee₁ b v) ∧
        (∃ B : Arm R d N p K K, WilsonReflectedRestoredStation.Situated R h.le A B) ∧
        ∀ factor:ℂ, ‖factor‖≤1 → ∃E, WilsonReflectedPublicSignedFare.Restored R A h.le top factor
          ((2+Extra.Histories.Motion.orbitCost ((C₀).labels.level d))*C*((β f)^q)⁻¹*fee₁ b v) E

private theorem bind {N p f K d:ℕ}(A:Arm R d N p f K)(Y:(C₀).label d)(turn:Motion)
    (c:Site ((C₀).side f p))(begin:f≤K)(live:K≤N)(dose:ℂ)(row:Three G ((C₀).side f p))
    (wallet head savings:ℝ) (Q E:Coefficient ((C₀).labels.level d) ((C₀).side f p))
    (src:A.Y=Y)(b:A.b=turn.2)(s:A.s=turn.1)(o:A.o=c)
    (form:Q.Format c (C₀).params ((C₀).path.rep N p f))
    (size:((C₀).labels.level d).coeffSize Q.x≤head)
    (paid:Q.remBound c ((C₀).path.rep N p f) (kappa (C₀).path f) wallet)
    (regular:row.2.1=Q.exponentialEntry c ((C₀).localSection d) ((C₀).path.rep N p f))
    (forced:profile ((C₀).path.rep N p f).activities row.2.2=
        profile ((C₀).path.rep N p f).activities Q.forced)
    (field:Q.density c ((C₀).localSection d) ((C₀).path.rep N p f)=row.1)
    (heard:∀L,row.1 L=dose*(((C₀).path.rep N p f).eval L:ℂ)*
        WilsonReflectedOriginalTwoDeposit.held R (WilsonReflectedPlacedArm.original R d
            (begin.trans live) Y turn.2 turn.1 c) f L)
    (replaced:WilsonReflectedPublicSignedFare.Restored R A begin live dose savings E):
    WilsonReflectedPublicGuardedColumns.Joined R A begin live dose row wallet head savings Q E :=by
  subst Y
  subst c
  apply WilsonReflectedPublicGuardedColumns.deposited R A begin live dose row Q E form size paid
    regular forced field _ replaced
  have pair:(A.s,A.b)=turn:=Prod.ext s b
  subst turn
  exact heard

private theorem clip (a:ℝ)(one:1≤a):‖(a:ℂ)⁻¹‖≤1:=by
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_of_lt_of_le (by norm_num: (0:ℝ)<1) one)]
  exact inv_le_one_of_one_le₀ one

private theorem attach {N p f K d:ℕ} {X:Type} (t T q jets:ℕ) (C:ℝ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)(date:Bool→ℕ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (h:f<K)(start:∀b,date b≤f)(top:K≤N)
    (stock:Inventory (R:=R) t T book fee₁ V u est (h.le.trans top))
    (both:Stock (R:=R) (p:=p) q jets C book fee₁ date M h start top)
    (b₀:Bool)(v₀:X)(turn:Motion)(c:Site ((C₀).side f p))
    (heard:∀L, (marked R (N:=N) 0 turn c V u
      (reduce (offer R (book b₀ v₀) est (h.le.trans top))) f).1 L =
      (((charge (offer R (book b₀ v₀) est (h.le.trans top)):ℝ):ℂ)⁻¹)*
      (((C₀).path.rep N p f).eval L:ℂ)*WilsonReflectedOriginalTwoDeposit.held R
        (WilsonReflectedPlacedArm.original R d (h.le.trans top) (book b₀ v₀) turn.2 turn.1 c) f L):
    Item (R:=R) q jets C (book b₀ v₀) (fee₁ b₀ v₀) (date b₀) (M b₀)
      turn c V u est h (start _) top := by
  unfold Item
  intro y data j w row wage Ω
  have unary := stock.1
  obtain ⟨ticket,offerReceipt⟩:=both b₀ v₀
  obtain ⟨A,src,weight,b,s,o,_,nested,sale⟩:=offerReceipt turn.2 turn.1 c
  refine ⟨ticket,A,src,weight,b,s,o,nested,?_⟩
  have one:1≤charge y:=le_max_left _ _
  let dose:ℂ:=((charge y:ℝ):ℂ)⁻¹
  have affordable:‖dose‖≤1:=clip (charge y) one
  obtain ⟨E,replaced⟩:=sale dose affordable
  obtain ⟨Q,form,size,paid,regular,forced,field⟩:=unary b₀ v₀ turn c
  refine ⟨Q,E,?_⟩
  exact bind A (book b₀ v₀) turn c h.le top dose row wage (Ω*(1+wage))
    ((2+Ω)*C*((β f)^q)⁻¹*fee₁ b₀ v₀) Q E src b s o form size paid regular forced field heard replaced

private theorem realize {N p f K d:ℕ} {X:Type} (t T q jets:ℕ) (C:ℝ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)(date:Bool→ℕ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (h:f<K)(start:∀b,date b≤f)(top:K≤N)
    (refs:∀ e≤d,(C₀).ref e≤N)
    (enrolled:Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p d
      (digits R N p 0) V u)
    (stock:Inventory (R:=R) t T book fee₁ V u est (h.le.trans top))
    (both:Stock (R:=R) (p:=p) q jets C book fee₁ date M h start top):
    Dossier (R:=R) t T q jets C book fee₁ date V u est M h start top := by
  obtain ⟨unary,joint⟩:=stock
  unfold Dossier
  intro I fi di weak v turn c names sep x y data
  obtain ⟨charges,post,lawful⟩:=joint I weak v turn c names sep
  refine ⟨charges,post,?_,lawful⟩
  have heard:=WilsonReflectedPublicFiledSingle.original R (fun _:I=>d) x (fun _=>V) (fun _=>u)
    (fun _=>est) (h.le.trans top) (fun _=>enrolled) (fun _=>refs) turn c names t post
  exact fun i=>attach t T q jets C book fee₁ date V u est M h start top ⟨unary,joint⟩ both
    (weak i) (v i) (turn i) (c i) (heard i)

theorem original (simple:G.Simple) (bliss:Bliss F l z H) (slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (width:∀i,1≤((lev).budget i).supportExponent)(capWidth:∀i,((lev).budget i).supportExponent≤100)
    (law:OPE.Therm.Poetry lev) (D d T q jets:ℕ) (cap:d≤D):
    ∃t≥D+3, ∃C:ℝ,0<C ∧ ∀ᶠ r in trail, ∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D≤k}{U:Spin.change S d}
      (P:Pair F stock cap W fits U r),W.checked order H k→W.wheel.r=r→
    let m:=max stock.j W.k
    let f:=WilsonInvariantActionPosition.berth R 5 m
    let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
    ∃h:f<K, ∃start:∀b,station F P b≤f, ∀N p (top:K≤N),
    ∃(V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p),
    Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p d (digits R N p 0) V u ∧
    ∃M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d,
      Dossier (R:=R) t T q jets C (fun b v=>(P.arm b v).source (N,p)) (fee F P)
        (station F P) V u est M h start top :=by
  obtain ⟨t,degree,estate⟩:=WilsonReflectedPublicOpticalEstate.original F simple bliss slow shop D d T cap
  obtain ⟨C,cp,joins⟩:=WilsonReflectedPublicOpticalSwaps.original F simple bliss slow shop width capWidth law D d T q jets cap
  let first:=(Finset.range (d+1)).sup (C₀).ref
  refine ⟨t,degree,C,cp,?_⟩
  filter_upwards [estate,joins,WilsonReflectedPublicStationLate.original F simple bliss T first]
    with r stored trade late k stock W fits U P check exactR m f K
  obtain ⟨h,start,buy⟩:=trade P check exactR
  refine ⟨h,start,?_⟩
  intro N p top
  have deep:f<N:=h.trans_le top
  obtain ⟨V,u,est,enrolled,unary,joint⟩:=stored P check exactR p N deep
  obtain ⟨M,both⟩:=buy N p top
  refine ⟨V,u,est,enrolled,M,?_⟩
  have refs (e:ℕ)(he:e≤d):(C₀).ref e≤N:=
    (Finset.le_sup (f:=(C₀).ref) (Finset.mem_range.mpr (Nat.lt_succ_of_le he))).trans
      ((late P check exactR false).trans ((start false).trans deep.le))
  exact realize t T q jets C (fun b v=>(P.arm b v).source (N,p)) (fee F P) (station F P)
    V u est M h start top refs enrolled ⟨unary,joint⟩ both

end YM.Integration.WilsonReflectedPublicGuardedEstate
end
