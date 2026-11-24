import YM.FVA2.ColumnPrice
import YM.FVA2.LiftedLabels
/-! # Exact mixed top columns realize the `Pencil` channel. Source system for regulators (pre physical normalization). -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Track
open Filter Topology Finset Function PowerSeries
open MS MS.Local MS.Landau MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Puff.SplitP MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater MS.Native MS.Native.Wilsonian MS.SpaceOut MS.Swirl.Near MS.Menus MS.Fleet
open Based PairCoords Modes Source Clock Paper Score Lattice Gauge
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.BlockGauge MultiGauge.Splice FormalOPE.RG10.InversionTop
open Wilson Trans PertExtension.Series PertExtension
open scoped Topology Classical ContDiff
variable {U G' J W:Type}
variable {G:Gauge}{n:Side}{B: Local.Physical.Deck G} (D:Warehouse G)
local notation "Fκ"=> Wilson.Field G n
local notation "L"=> plan G n
local notation "Λ"=> Orb.tray G
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
local notation "ιψ"=> Boson.sharp (bell m (J:=J)) φ (bell_even m)
local notation "↓ψ"=> Paper.track ψ

-- or define later for he implicit

section points
variable (he:Even n.val) {d:ℕ}(u:Site n)(i:D.Atom d)

def loadStamp := Source.stamp (D.poised d i) u (D.awake d i).low

def singleStamp : Ticket Fκ:= Source.seated u (D.grade d i) (Plate.bare (D.S d) i)
lemma loadedStamp : X^(D.grade d i) * singleStamp D u i = MultiGauge.Stack.rise (Wilson.slice L (loadStamp D u i).stencil):= roster (D.poised d i) u (D.awake d i).low
lemma loadedCost : seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (Book.levels (D.grade d i) (D.artifact d i))) = Score.bore m (singleStamp D u i):= Source.charged_seat (D.poised d i) u m b (D.grade d i)
lemma stamp_honest : Wilson.Honest (loadStamp D u i).stencil:= Source.tree_honest (D.poised d i) u
lemma stamp_phys : Wilson.Physical (loadStamp D u i).stencil:= Source.treeGauge (D.poised d i) u
end points
section slots
-- no fusions! any coincident fields at this one regulator. correlated Choice order via occurrence addresses
variable {I:Type}[DecidableEq I](p:I→Site n)(d:I→ℕ)
variable (u:(i:I)→D.Atom (d i))(s:Finset I)

def Seals i := loadStamp D (p i) (u i)
-- comparison. observation on finite subset s.
def Packed := ∏ i∈s,singleStamp D (p i) (u i)
local notation "Sκ"=> (Seals D p d u)
local notation "Vκ"=> Stamp.shafts Sκ s
lemma packedPhysical : Wilson.Physical Vκ:= by
   induction s using Finset.induction_on with| empty=> unfold Stamp.shafts; rw [Finset.prod_empty]; exact Wilson.Physical.one G n| insert a s hi ih=> unfold Stamp.shafts; rw [Finset.prod_insert hi]; exact fun g h q=> congr_arg₂ (·*·) (stamp_phys D (p a) (u a) g h q) (ih g h q)
lemma packedHonest : Wilson.Honest Vκ:=by
   induction s using Finset.induction_on with| empty=> unfold Stamp.shafts; rw [Finset.prod_empty]; exact one_honest| insert a s hi ih=> unfold Stamp.shafts; rw [Finset.prod_insert hi]; exact ContDiffAt.mul (stamp_honest D (p a) (u a)) ih
lemma shift_stamp : X^(Stamp.degrees Sκ s) * Packed D p d u s=MultiGauge.Stack.rise (Wilson.slice L Vκ):= by
   induction s using Finset.induction_on with
   | empty => unfold Stamp.shafts Stamp.degrees Packed; rw [Finset.prod_empty,Finset.prod_empty,Finset.sum_empty,pow_zero,mul_one]; exact (MultiGauge.Stack.rise_one).symm
   | insert a s h ih =>
      rw [ Stamp.degrees,Finset.sum_insert h, Packed, Finset.prod_insert h,pow_add, Stamp.shafts, Finset.prod_insert h ];
      let F:PowerSeries (Permit Fκ):= X^ Stamp.degrees (Seals D p d u) s
      change X^(D.grade _ (u a)) * F * (_ * Packed D p d u s)= MultiGauge.Stack.rise ( (Wilson.slice L ((loadStamp D (p a) (u a)).stencil)) * (Wilson.slice L (Stamp.shafts Sκ s))) -- fix notation
      rw [MultiGauge.Stack.rise_mul (g:= slice L (Stamp.shafts Sκ s)) ((slice_hot L (stamp_phys D (p a) (u a)) (stamp_honest D (p a) (u a))).of_le le_top) ((slice_hot L (packedPhysical D p d u s) (packedHonest D p d u s)).of_le le_top), ← ih, ← loadedStamp ]; unfold F; ring

variable (he: Even n.val)
local notation "ν"=> (Chart.tangent G (staple n).Bulk)
lemma pressed : PowerSeries.mk (Orb.diag (Orb.restrictedO Vκ)) = X^ (Stamp.degrees Sκ s) * exchange he Λ (Packed D p d u s) := by
    have hz:= (tree_identity L he Λ (Orb.traySpec G) (packedPhysical D p d u s) (packedHonest D p d u s)).trans ( (exchange_fields he Λ (Orb.traySpec G) Vκ ((slice_hot L (packedPhysical D p d u s) (packedHonest D p d u s)).of_le le_top)).symm )
    let v:=Stamp.degrees Sκ s; rw [show PowerSeries.mk (Orb.diag (Orb.restrictedO Vκ))= _ from hz, ← shift_stamp ]; unfold exchange enjoy; rw [ mul_left_comm (supportV G n Λ) (X^v), MultiGauge.Stack.taking (Trans.price G he) ν ]; ring
lemma pays_rows : Channel.realRead Sκ s=exchange he Λ (Packed D p d u s):= by unfold Channel.realRead; rw [pressed D p d u s he,MultiGauge.Stack.drop_mul]
end slots
section bridges
variable (he:Even n.val) {d:ℕ}(u:Site n)(i:Glyph B d)
variable (t: Team) (x:ℝ) (Z: Acts B d)
abbrev Beamers (D:Warehouse G) (B:Local.Physical.Deck G)(d:ℕ) := (i:Glyph B d) × (D.Atom i.size)


local notation "κ"=> Clock.warp ψ (shift t x) (share t x)

def tariff (Q: Beamers D B d) : PowerSeries ℝ := (Channel.credits Q.1 x Z)*PowerSeries.C (D.prices B Q.1.size Q.1.grade Q.1.2.2 Q.2)
def beyond (Q:Beamers D B d): Price ψ:= currency ψ (into (tariff D x Z Q)) * κ (ιψ (singleStamp D u Q.2))
lemma person_shift {d:ℕ} (v:D.Atom d): ↓ψ (κ (ιψ (singleStamp D u v))) = seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (wobble G (Stripped t) x (D.inkB d v))) := by
    rw [ Near.strip_wobble,Clock.sensible,show ∀ f:SpecB (Pos G n), seriesPlug (mkPlug m b) (substitute (shift t x) f)=_ from fun f=> Clock.sensible _ f,warp_acts]; exact congr_arg _ (loadedCost D m b u v).symm

private lemma direct_steam (w:ℝ) (P:Price ψ) : ↓ψ (currency ψ (into (PowerSeries.C w))*P)=(w:ℂ) • ↓ψ P:= by
   unfold currency into; rw [PowerSeries.map_C,map_C]; funext i; rw [ Paper.trackC_mul,cash1,coin_product]; rfl
lemma party : (↓ψ (∑ j:D.Atom i.size,beyond D m (J:=J) u t x Z ⟨ i,j ⟩ )) = seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) ( pairW (LinearMap.lsmul ℂ ( Dot G Lattice.Cover )) (fun j=>oil Z i j x) (Glyph.preambleM (D.native B) (Stripped t) i x)) ):= by
   unfold beyond tariff; simp only [map_sum,map_mul,mul_assoc]; -- expand singly
   simp_rw [currency_pair ψ (into (Channel.credits i x Z)), direct_steam, person_shift D m b]; unfold Glyph.preambleM; rw [ ← map_sum ];
   change pairW _ _ _= seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (pairW _ _ ( wobble G (Stripped t) x ( Warehouse.code D _ _) ) ) ); unfold Warehouse.code; rw [map_sum,Channel.oilCred]; simp_rw [← map_smul, ← map_sum] 
   have hv {A H:Type} [AddCommGroup A][AddCommGroup H][Module ℂ A][Module ℂ H] (PhiT:A→ₗ[ℂ] H)(P:T A)(Q:T ℂ): pairW (LinearMap.lsmul ℂ H) Q (pointL ℕ PhiT P)=pointL ℕ PhiT (pairW (LinearMap.lsmul ℂ A) Q P):= by funext i; rw [paired]; change _= PhiT (pairW _ _ _ i); simp_rw [paired,map_sum,LinearMap.lsmul_apply,map_smul]; rfl
   rw [show pairW _ _ _ = _ from hv (plug (mkPlug m b)) _ _,hv]

def lantern : Price ψ := ∑ i:Beamers D B d,beyond D m u t x Z i
lemma seats : ↓ψ (lantern D m (J:=J) u t x Z) = seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (Menus.rentM (D.native B) (Stripped t) Z x)):= by
    let F(i:Glyph B d) := pairW (LinearMap.lsmul ℂ ( Dot G Lattice.Cover )) (fun j=>oil Z i j x) (Glyph.preambleM (D.native B) (Stripped t) i x)
    have he : Menus.rentM (D.native B) (Stripped t) Z x = ∑ i:Glyph B d,F i:= funext fun k=>by rw [Finset.sum_apply]; rfl
    unfold lantern; rw [ Fintype.sum_sigma, map_sum,he,map_sum,map_sum ]; exact Finset.sum_congr rfl fun j _=> party D m b u j t x Z
end bridges

section fuel
variable (he:Even n.val){I:Type}[LinearOrder I]
variable (d:I→ℕ)(Z:(i:I)→ Acts B (d i))
local notation "ℍ"=> λ i:I=> Glyph B (d i)
variable (t: Team)(x:ℝ)(A:Lattice.Cover)(c:I→Lattice.Cover)
-- important: implicit U,J typing will be checked
variable [Fintype U][Fintype J][DecidableEq J]
local notation "ρ"=> (Currency m (J:=J) he)
local notation "κ"=> Clock.warp ψ (shift t x) (share t x)

-- c address relative to anchor A (possibly outside representative positive half-torus).
def request i:= Menus.rentM (D.native B) (Stripped t) (Z i)
local notation "Cκ"=> Track.request D d Z t
local notation "Pκ"=> Seals D
local notation "Yκ"=> Channel.coord n A c

omit [LinearOrder I] in
lemma request_friendly : Badge Cκ:= fun _=> billRentM _ _ _

variable (s:Finset I)
local notation "FΩ"=>Font σbranch (posMark G n Cκ x A c) s
local notation "Fζ"=> ∏ i∈s,lantern D m (J:=J) (Yκ i) t x (Z i)

omit [Fintype U] [Fintype J] [DecidableEq J] in
private lemma ties : (↓ψ Fζ)= seriesPlug (mkPlug m b) FΩ:= by
   rw [seriesPlug_sources (mkPlug m b) (lawful m b)]
   let V:= seriesPlug (mkPlug m b) ∘ posMark G n Cκ x A c; let A0 i:= lantern D m (J:=J) (Yκ i) t x (Z i)
   have he (i:I): ↓ψ (A0 i)=V {i}:= by unfold A0 V; rw [Function.comp_apply,pin_one G n Cκ]; exact seats D m b _ t _ _
   have ht (i: Finset I)(hs:i.card ≠ 1): V i=0:= by unfold V; rw [ Function.comp_apply, pin_off _ _ hs,map_zero ]
   have hv(i:Finset I): V i∈ (PermV ψ).guard:= by
       by_cases h:i.card=1; · obtain ⟨p,rfl⟩:= Finset.card_eq_one.mp h; rw [← he p]; exact track_full _
       rw [ht i h]; exact (PermV ψ).guard.zero_mem -- layout
   change ↓ψ (∏ i∈s,A0 i)= Cheer _ (marked I) V s
   induction s using Finset.induction_on with| empty=> rw [Finset.prod_empty,track_one]; exact (Puff.Stencil.simple_E _ _ (marked I) (ht ∅ (by simp))).symm | insert i s h ih=>rw [Finset.prod_insert h,pair, he, ih, Puff.Stencil.cheers (PermV ψ) hv ht s i h]

-- each occurrence chooses a Glyph from its own size up to its field's horizon
abbrev Crew (D:Warehouse G)(B:Local.Physical.Deck G)(d:I→ℕ)(s:Finset I) := (i:s)→Beamers D B (d i.val)
local notation "Σκ"=>Crew D B d s
local notation "δC"=> d ∘ ( Subtype.val:s→I )
local notation "δZ"=> fun g:s=> Z g.val

def people (u:Crew D B d s):= Packed D (n:=n) (Yκ ∘ Subtype.val) (fun i=>(u i).1.size) (fun i=>(u i).2) Finset.univ

def debt (u:Crew D B d s) : PowerSeries ℝ:= ∏ i:s, tariff D x (Z i.val) (u i)
omit [Fintype U] [Fintype J] [DecidableEq J] in
lemma packages : (Fζ) = ∑ u:Σκ, currency ψ (into (debt D d Z x s u)) * κ (ιψ (people D (n:=n) d A c s u)):= by
     rw [← Finset.prod_attach,show s.attach=Finset.univ from rfl]; unfold lantern; rw [Fintype.prod_sum]; -- defeq dependent
     refine Finset.sum_congr rfl fun i _=>?_ ; unfold debt people Packed beyond; rw [Finset.prod_mul_distrib]; -- maybe orientation of sub type
     rw [map_prod,map_prod,map_prod,map_prod]; rfl

-- this provides the final formal finite cost with all marks in their slots of the given horizon,
-- mixed by `Acts` **after** (t,x)-specified bare coupling shift.
def deckRead (D:Warehouse G)(n:Side)(d:I→ℕ)(t:Team)(x:ℝ)(A:Lattice.Cover)(c:I→Lattice.Cover)(s:Finset I)(u:Crew D B d s): PowerSeries ℝ:=
    Clock.reprℝ t x (Channel.realRead (Seals D ((Channel.coord n A c) ∘ Subtype.val) (fun i=>(u i).1.size) (fun i=>(u i).2)) Finset.univ)
def ticketRead (D:Warehouse G)(n:Side)(d:I→ℕ)(t:Team)(x:ℝ)(Z:(i:I)→ Acts B (d i))(A:Lattice.Cover)(c:I→Lattice.Cover)(s:Finset I): PowerSeries ℝ:=
    ∑ u:Crew D B d s, debt D d Z x s u * deckRead D n d t x A c s u

include he
lemma bench (u:Σκ): Endμ ρ ψ (↓ψ (κ (Score.total Λ m b))) (↓ψ (κ (ιψ (people D (n:=n) d A c s u)))) (netE (deckRead D n d t x A c s u)) := by
   unfold deckRead; rw [warp_acts,warp_acts, pays_rows D _ _ _ _ he,compℝ ]; exact Clock.rotate ρ (share ..) (at_end he Λ (Orb.traySpec G) m b _) (by rw [tracking,total_min _ (Orb.traySpec G)]; rfl)

set_option maxHeartbeats 210000 in
lemma sell : Endμ ρ ψ (↓ψ (κ (Score.total Λ m b))) (seriesPlug (mkPlug m b) FΩ) (netE (ticketRead D n d t x Z A c s)):= by
    rw [← ties D m b, packages D m,ticketRead,out_real,map_sum into,map_sum Clock.out]; apply Clock.end_sum ρ (Q:= κ (Score.total Λ m b)) (I:=Crew D B d s) (S:=univ) (F:=fun i=> currency ψ (into (debt D d Z x s i))*κ (ιψ (people D (n:=n) d A c s i))) (Z:=fun i=> out (into (debt D d Z x s i * deckRead D n d t x A c s i)))
    intro i hi; rw [map_mul into,out_prod,← out_real (deckRead D n d t x A c s i) ]; exact Clock.end_scalar ρ (bench D m b he d t x A c s i) (into (debt D d Z x s i))

include m b in
lemma revenue : Endμ (Based.cov G n true) σbranch (posNRG G n (Stripped t) x true) FΩ (netE (ticketRead D n d t x Z A c s)):= by
    rw [compress m b he]; apply (plug_end _ _ (lawful m b) (bulk_bounded G n (Stripped t) x true) (pin_bounded G n _ (request_friendly D d Z t) x A c s) _).mp
    rw [pose_shift, show ∀ f:SpecB (Pos G n), seriesPlug (mkPlug m b) (substitute (shift t x) f)=_ from fun f=> Clock.sensible _ f, initial_in he Λ (Orb.traySpec G) m b, ← warp_acts (h:=share t x) ]; exact sell D m b he d Z t x A c s

/-- **Finite-regulator identification with MS input**. Unpacked form
 gives the coefficient system using exactly the supplied bare Mark_T pinned cost on the marked side, and
 Wilson realRead/Orb.diag and common Team.clock on the consumer side. Arg `b` literal true to charge
 inversion. No regulator estimates hidden. Basis compression is a proof tool (no hypothesis). Markers
 at the same position allowed. Also includes unmarked readings. -/
theorem finite_bridge (X:T ℂ): PhysicalSum G t x n true s c A Cκ X ↔
     netE (ticketRead D n d t x Z A c s)= X:= by
   rw [positionEnd G n _ _ true _ (request_friendly D d Z t)]; let U' := Fin (Module.finrank ℝ (Wilson.Field G n)); let J':= Fin (Module.finrank ℝ (Param G n)); have ht:= revenue D (Module.finBasis ℝ (Wilson.Field G n)) (Module.finBasis ℝ (Param G n)) he d Z t x A c s; exact ⟨fun h=> classicalμ (charge_zero ..) ht h, fun h=> h ▸ ht ⟩

end fuel
end YM.FVA2.Track
