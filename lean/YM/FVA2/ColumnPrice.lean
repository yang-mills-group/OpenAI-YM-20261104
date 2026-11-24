import YM.FVA2.CouplingSubstitution
import YM.FVA2.RankStamp
import YM.FormalOPE.RG10.MultiGauge.Membership

/-!
# Bare Wilson physical insertion matrix readout (to Bare-MS gauges, `b=true`)

`finite_bridge`. At every regulator not just separated points. Uses precisely
YM.PertExtension diagonal convention and Laurent prefactors per field slot.
Geometry with period address base at `x+c w`, tests and optional scalar log-reg
weights with all marks (finite source horizon dependent on slot). This is equality
of the prescribed Wilson coefficients of `NativeDictionary` stencils to the
required `PhysicalSum`, including unmarked action and source clocks.
Not identifying the supplied prescription's `rent` with bare Gram-renormalized
fields yet. In particular these field columns need not preserve leading identity.
Inputs `z,f` etc in companion tasks can be these exact real series at UV regulator.
No analytic denominator estimate (full actual `Endμ` both sides, conditional RG
 at given field is covered in route files). Position errors only later.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Channel
open Filter Topology Finset Function PowerSeries
open MS MS.Local MS.Landau MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Puff.SplitP MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater MS.Native MS.Native.Wilsonian MS.SpaceOut MS.Swirl.Near MS.Menus MS.Fleet
open Based PairCoords Modes Source Clock Paper Score Lattice Gauge
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.BlockGauge MultiGauge.Splice FormalOPE.RG10.InversionTop
open Wilson Trans PertExtension.Series PertExtension
open scoped Topology Classical ContDiff
variable {U G' J W:Type}
variable {G:Gauge}{n:Side}{B: Local.Physical.Deck G} (D:NativeDictionary B)
local notation "Fκ"=> Wilson.Field G n
local notation "L"=> plan G n
local notation "Λ"=> Orb.tray G
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
local notation "ιψ"=> Boson.sharp (bell m (J:=J)) φ (bell_even m)
local notation "↓ψ"=> Paper.track ψ

-- or define later for he implicit

section points
variable (he:Even n.val) {d:ℕ}(u:Site n)(i:Glyph B d)

def loadStamp := Source.stamp (D.stamps i.size i.grade i.2.2) u (D.book.levels i.size i.grade i.2.2).low

def singleStamp : Ticket Fκ:= Source.seated u i.grade (D.formula i.size i.grade i.2.2)
lemma loadedStamp : X^i.grade * singleStamp D u i = MultiGauge.Stack.rise (Wilson.slice L (loadStamp D u i).stencil):= roster (D.stamps i.size i.grade i.2.2) u (D.book.levels i.size i.grade i.2.2).low
lemma loadedCost : seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (Book.levels i.grade (Glyph.lit D.book i))) = Score.bore m (singleStamp D u i):= Source.charged_seat (D.stamps i.size i.grade i.2.2) u m b i.grade
lemma stamp_honest : Wilson.Honest (loadStamp D u i).stencil:= Source.tree_honest (D.stamps i.size i.grade i.2.2) u
lemma stamp_phys : Wilson.Physical (loadStamp D u i).stencil:= Source.treeGauge (D.stamps i.size i.grade i.2.2) u
variable (t: Team) (x:ℝ) (Z: Acts B d)
def credits : PowerSeries ℝ := mk fun h:ℕ=> ((Z h).register i).eval x
-- signature
lemma oilCred : (out (into (credits i x Z))) = fun j=> Menus.oil Z i j x:= by
    ext1 k; rw [out_coeff,into_coeff, credits,coeff_mk]; rfl

local notation "κ"=> Clock.warp ψ (shift t x) (share t x)

def beyon : Price ψ:= currency ψ (into (credits i x Z)) * κ (ιψ (singleStamp D u i))
lemma seat_shift : ↓ψ (κ (ιψ (singleStamp D u i))) = seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (Glyph.preamble D.book (Stripped t) i x)) := by
    rw [Glyph.preamble, Near.strip_wobble,Clock.sensible,show ∀ f:SpecB (Pos G n), seriesPlug (mkPlug m b) (substitute (shift t x) f)=_ from fun f=> Clock.sensible _ f,warp_acts]; exact congr_arg _ (loadedCost D m b u i).symm

def lantern : Price ψ := ∑ i:Glyph B d,beyon D m u i t x Z
lemma seats : ↓ψ (lantern D m (J:=J) u t x Z)=seriesPlug (mkPlug m b) (pointL ℕ (Based.place G n u) (Menus.rent D.book (Stripped t) Z x)) := by
   unfold lantern; simp_rw [map_sum,beyon,currency_pair,seat_shift D m b]
   funext k; change _=plug _ (Based.place G n u (∑ i:Glyph B d,∑ j∈antidiagonal k,oil Z i j.1 x • Glyph.preamble D.book (Stripped t) i x j.2 )); rw [map_sum,map_sum,Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [paired,map_sum,map_sum]; apply Finset.sum_congr rfl; intro p _; rw [map_smul,map_smul,oilCred]; rfl
end points
section slots
-- no fusions! any coincident fields at this one regulator. correlated Choice order via occurrence addresses
variable {I:Type}[DecidableEq I](p:I→Site n)(d:I→ℕ)
variable (u:(i:I)→Glyph B (d i))(s:Finset I)

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
      change X^(u a).grade * F * (_ * Packed D p d u s)= MultiGauge.Stack.rise ( (Wilson.slice L ((loadStamp D (p a) (u a)).stencil)) * (Wilson.slice L (Stamp.shafts Sκ s))) -- fix notation
      rw [MultiGauge.Stack.rise_mul (g:= slice L (Stamp.shafts Sκ s)) ((slice_hot L (stamp_phys D (p a) (u a)) (stamp_honest D (p a) (u a))).of_le le_top) ((slice_hot L (packedPhysical D p d u s) (packedHonest D p d u s)).of_le le_top), ← ih, ← loadedStamp ]; unfold F; ring

variable (he: Even n.val)
local notation "ν"=> (Chart.tangent G (staple n).Bulk)
lemma pressed : PowerSeries.mk (Orb.diag (Orb.restrictedO Vκ)) = X^ (Stamp.degrees Sκ s) * exchange he Λ (Packed D p d u s) := by
    have hz:= (tree_identity L he Λ (Orb.traySpec G) (packedPhysical D p d u s) (packedHonest D p d u s)).trans ( (exchange_fields he Λ (Orb.traySpec G) Vκ ((slice_hot L (packedPhysical D p d u s) (packedHonest D p d u s)).of_le le_top)).symm )
    let v:=Stamp.degrees Sκ s; rw [show PowerSeries.mk (Orb.diag (Orb.restrictedO Vκ))= _ from hz, ← shift_stamp ]; unfold exchange enjoy; rw [ mul_left_comm (supportV G n Λ) (X^v), MultiGauge.Stack.taking (Trans.price G he) ν ]; ring
-- will expose canonical bare coefficients and costs

def realRead (O:I→Stamp G n)(s:Finset I):= MultiGauge.Stack.drop (Stamp.degrees O s) (PowerSeries.mk (Orb.diag (Orb.restrictedO (Stamp.shafts O s))))
lemma pays_rows : realRead Sκ s=exchange he Λ (Packed D p d u s):= by unfold realRead; rw [pressed D p d u s he,MultiGauge.Stack.drop_mul]
end slots
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
def coord (n:Side)(A:Lattice.Cover)(c:I→Lattice.Cover)(i:I): Site n:=wrap n (A+c i)
def request i:= Menus.rent D.book (Stripped t) (Z i)
local notation "Cκ"=> Channel.request D d Z t
local notation "Pκ"=> Seals D
local notation "Yκ"=> coord n A c

omit [LinearOrder I] in
lemma request_friendly : Badge Cκ:= fun _=> billRent _ _ _

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
abbrev Crew (B:Local.Physical.Deck G)(d:I→ℕ)(s:Finset I) := (i:s)→Glyph B (d i.val)
local notation "Σκ"=>Crew B d s
local notation "δC"=> d ∘ ( Subtype.val:s→I )
local notation "δZ"=> fun g:s=> Z g.val

def people (u:Σκ):= Packed D (n:=n) (Yκ ∘ Subtype.val) (d ∘ (Subtype.val:s→I)) u Finset.univ

def debt (u:Crew B d s) : PowerSeries ℝ:= ∏ i:s, credits (u i) x (Z i.val)
omit [Fintype U] [Fintype J] [DecidableEq J] in
lemma packages : (Fζ) = ∑ u:Σκ, currency ψ (into (debt d Z x s u)) * κ (ιψ (people D (n:=n) d A c s u)):= by
     rw [← Finset.prod_attach,show s.attach=Finset.univ from rfl]; unfold lantern; rw [Fintype.prod_sum]; -- defeq dependent
     refine Finset.sum_congr rfl fun i _=>?_ ; unfold debt people Packed beyon; rw [Finset.prod_mul_distrib]; -- maybe orientation of sub type
     rw [map_prod,map_prod,map_prod,map_prod]; rfl

-- this provides the final formal finite cost with all marks in their slots of the given horizon,
-- mixed by `Acts` **after** (t,x)-specified bare coupling shift.
def deckRead (D:NativeDictionary B)(n:Side)(d:I→ℕ)(t:Team)(x:ℝ)(A:Lattice.Cover)(c:I→Lattice.Cover)(s:Finset I)(u:Crew B d s): PowerSeries ℝ:=
    Clock.reprℝ t x (realRead (Seals D ((coord n A c) ∘ Subtype.val) (d ∘ (Subtype.val:s→I)) u) Finset.univ)
def ticketRead (D:NativeDictionary B)(n:Side)(d:I→ℕ)(t:Team)(x:ℝ)(Z:(i:I)→ Acts B (d i))(A:Lattice.Cover)(c:I→Lattice.Cover)(s:Finset I): PowerSeries ℝ:=
    ∑ u:Crew B d s, debt d Z x s u * deckRead D n d t x A c s u

include he
lemma bench (u:Σκ): Endμ ρ ψ (↓ψ (κ (Score.total Λ m b))) (↓ψ (κ (ιψ (people D (n:=n) d A c s u)))) (netE (deckRead D n d t x A c s u)) := by
   unfold deckRead; rw [warp_acts,warp_acts, pays_rows D _ _ _ _ he,compℝ ]; exact Clock.rotate ρ (share ..) (at_end he Λ (Orb.traySpec G) m b _) (by rw [tracking,total_min _ (Orb.traySpec G)]; rfl)

set_option maxHeartbeats 210000 in
lemma sell : Endμ ρ ψ (↓ψ (κ (Score.total Λ m b))) (seriesPlug (mkPlug m b) FΩ) (netE (ticketRead D n d t x Z A c s)):= by
    rw [← ties D m b, packages D m,ticketRead,out_real,map_sum into,map_sum Clock.out]; apply Clock.end_sum ρ (Q:= κ (Score.total Λ m b)) (I:=Crew B d s) (S:=univ) (F:=fun i=> currency ψ (into (debt d Z x s i))*κ (ιψ (people D (n:=n) d A c s i))) (Z:=fun i=> out (into (debt d Z x s i * deckRead D n d t x A c s i)))
    intro i hi; rw [map_mul into,out_prod,← out_real (deckRead D n d t x A c s i) ]; exact Clock.end_scalar ρ (bench D m b he d t x A c s i) (into (debt d Z x s i))

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
end YM.FVA2.Channel
