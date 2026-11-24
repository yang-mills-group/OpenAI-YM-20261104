import YM.SignedWilsonExpansion.AxialBill
import YM.SignedWilsonExpansion.Grid.Economy
namespace YM.SignedWilsonExpansion.Overlap.Statement
/-! # Reading the ledger of two different plane energies back into phase story. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Plane MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land MS.Puff MS.Puff.Mom MS.Puff.SplitP MS.Puff.Engine MS.Puff.Actors
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace PhaseTilt PairWave Economy Duet Align
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O) (ν:ℝ)
local notation "v" => Press.portDeck G
local notation "Q" => (PowerSeries ℂ)
local notation "Ψ" => Equator.wave ν M 4
local notation "ι" => grade2 G
local notation "ζ" => (fun i:ι=> Land.read (MarkRows.address i))
abbrev index (s:Bool):Idx:= if s then 3 else 1
abbrev field (G:Gauge)(s:Bool): Sec G 4:= glow G (index s) (index s)
local notation "γ" => (fun s:Bool=>Energy.called (degreeX s) 2 G)
variable (l r:Bool)
local notation "E" => field G
lemma markl : (E l).val= Energy.raw G (degreeX l) 2:= by cases l <;> rfl
lemma lenses : E l =∑ i:grade2 G, (γ l i:ℂ) • (kind i):= by
   let b:= Theater.Resume v 4 2; let w:=Energy.here (degreeX l) 2 G; have hp:( Theater.Resume v 4 2 w ).val=Energy.off (degreeX l) 2 G:= by
      let v': Film0 G 4 2:= ⟨Energy.off (degreeX l) 2 G,Energy.admitted (degreeX l) 2⟩; refine congr_arg (fun a:Film0 G 4 2=> a.val) (?_ : Theater.Resume v 4 2 w=v'); exact ( Theater.craftK G 4 2 ).injective ( Subtype.ext ( ( honor v w ).trans ( Energy.over_color _ _ ).symm ) )
   apply Subtype.ext; obtain he:= ( Module.finBasis ℝ _ ).sum_repr w
   rw [markl, show Energy.raw G (degreeX l) 2=reduceEq ( Theater.Resume v 4 2 w ).val from (by rw [ hp, ← Energy.sectionE ]; exact ( On.lift_recover _ ).symm ), ← he, map_sum ]; simp_rw [map_smul]
   let T:Film0 G 4 2→ₗ[ℝ] WickPol G:= stageM G 4 2; change T (∑ i:ι, γ l i • Theater.Resume v 4 2 (( Module.finBasis ℝ _ ) i) ) = _; rw [ map_sum, AddSubmonoidClass.coe_finsetSum ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ map_smul ]; change γ l i • ( ( kind i ).val )=( (γ l i:ℂ) ) • ((kind i).val); exact (IsScalarTower.algebraMap_smul ℂ (γ l i) (kind i).val ).symm
abbrev address (G:Gauge)(l:Bool): Tags G 4 1:= fun _=> field G l
abbrev address2 (G:Gauge)(l r:Bool) : Tags G 4 2:= ![ field G l, field G r ]
local notation "K₁" => (Finset.univ (α:=Fin 1))
variable (y:Stage 1)
lemma singleF (t:ℕ): Ψ 1 y t ( address G l )=∑ j:ι, (γ l j:ℂ)*mon M y j ν t:= by
    let P:Module.Dual ℂ (Sec G 4):=(Ψ 1 y t).toLinearMap (address G l) 0; rw [ show Ψ 1 y t (address G l)=P (E l) from ?_, lenses,map_sum ]; swap; · apply congr_arg (Ψ 1 y t); exact (update_eq_self ..).symm
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [ _root_.map_smul ]; let w: Fin 1→Toon G 4:=fun _=> ζ i; have h:update (address G l) 0 (kind i)=Dframe.fill w:= funext fun k=> (by fin_cases k; simp only [Function.update_self]; rfl)
    rw [ show P ( kind i )=_ from ( congr_arg (Ψ 1 y t) h ),Equator.wave,ribbon ]; unfold continuum Landing.moondye Dial.tour; rw [ show K₁={0} from rfl, PairWave.equip ]; rfl
lemma begSingle : Ψ 1 y 0 ( address G l )=0:= by
    rw [ before ]; refine Eq.trans ?_ ( WickFace.single_off y (G:=G) (0:Fin 1) ( index l ) ( index l ) ); apply congr_arg ( Maxwell.Wick.moment G y.val ); funext i; fin_cases i; simp only [update_self]; rfl
local notation "kY" => Arrival.Schedule.plot
variable (p:Stage 2)
lemma ticket (t:ℕ): Ψ 2 p t (address2 G l r)= Duet.opposite M ( kY p.val ) l r ν t + Trunk.core ( fun t=> Ψ 1 y t ( address G l ) ) (fun t=> Ψ 1 y t ( address G r ) ) t:= by
    let A0:= Ψ 2 p t; let U:= address2 G l r; have he : A0 U=∑ i:grade2 G,∑ j:grade2 G, (γ l i:ℂ)*(γ r j:ℂ)*A0 ( Dframe.fill ( duo_t i j ) ):= by
       let W'(i:grade2 G):= update U 0 (kind i); let P:=A0.toLinearMap U 0
       rw [ show A0 U=P (E l) from ?_, lenses,map_sum ]; swap; · exact ( congr_arg A0 (update_eq_self ..) ).symm
       apply Finset.sum_congr rfl; intro i _; rw [ _root_.map_smul ]; let Q':=A0.toLinearMap ( W' i ) 1
       rw [ show P (kind i)=Q' (E r) from ?_,lenses,map_sum, Finset.smul_sum ]; swap; · apply congr_arg A0; rw [← show W' i 1=E r from (by unfold W'; simp [address2,U]) ]; exact (update_eq_self ..).symm
       apply Finset.sum_congr rfl; intro j _; rw [ map_smul ]; rw [show Q' (kind j)= A0 (Dframe.fill ( duo_t i j )) from (by apply congr_arg A0; funext i; fin_cases i <;> first| rfl| simp only [ Function.update_self,Function.update_of_ne (by decide : (0:Fin 2)≠1) ]; rfl ), smul_eq_mul,smul_eq_mul ]; ring
    change A0 U= _; rw [he]; unfold Duet.opposite; unfold A0; simp_rw [ PairWave.ledger M ν y p ];
    have hz(l:Bool): (fun t=> Ψ 1 y t ( address G l ))=∑ i:ι, (γ l i:ℂ) • mon M y i ν:= by funext t; rw [ singleF M ν l y t, Finset.sum_apply ]; rfl
    rw [ hz, hz ]; simp_rw [ mul_add,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.sum_apply,Finset.sum_add_distrib, Pi.smul_apply ]; congr 1; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by simp only [ smul_eq_mul ]; ring
variable (S: Land.Prescription (Press.portDeck G))(W':Initialize G)(h:G.Simple)(hs:TaylorOKF M (Press.wickInput W') S)
include hs h
include y in
lemma price2 : Ψ 2 p 2 (address2 G l r)=Duet.opposite M ( kY p.val ) l r ν 2:= by
    rw [ ticket M ν l r y p,biphase ]; have ht:Ψ 1 y 1=0:= PhaseTilt.parity_point h _ (FVA2.Parity.Invol.earns ν W' S M h hs ( d:=4 ) y.property); rw [show Finset.antidiagonal 2={(0,2),(1,1),(2,0)} from by decide,sum_insert (by decide),sum_insert (by decide),sum_singleton ]; rw [ begSingle M ν l y,begSingle M ν r y,zero_mul,mul_zero, ht ]; simp
lemma adjust (d v0:ℝ)(hh:d≠0)(he:p.val 1-p.val 0=timeLine d):
    Ψ 2 p 2 (address2 G l (!l))- Equator.wave (ν+v0) M 4 2 p 2 (address2 G l (!l))=
       (( -(2*( v0*Align.salaryQ G ))):ℝ ) • (Ψ 2 p 0 (dd G)):= by
    let q:= kY p.val; have hu : q 1-q 0= FourierGaussian.axis d:= by
       rw [ show q 1-q 0 = Theater.out (timeLine d) from (by rw [← he]; exact (_root_.map_sub ..).symm) ]; unfold timeLine FourierGaussian.axis; rw [ map_smul ]; rfl
    let y : Stage 1:=⟨ 0, fun _ _ _=> Subsingleton.elim ..⟩
    rw [price2 M ν l (!l) y p S W' h hs, price2 M (ν+v0) l (!l) y p S W' h hs,PairWave.pair_price M ν y p, ← neg_sub ( a:=Duet.opposite M q l (!l) (ν+v0) 2 ), Economy.income l M h q hh (Schedule.track p.property) hu,neg_smul ]
variable {V:Normalize.Store G}(K: Rose.Pick V)(hr:Favors.Horder S)(hu: Ace.UnitP S)
local notation "Z" => (PowerSeries.coeff 2 ( GroupS.gaugeM W' K M ν (-1) 4))
include hr hu
lemma tariff (H: WickFace.Holds p) : Manifest.response p (address2 G l (!l)) Z= (( -(2*Align.salaryQ G)):ℝ) • iris p (dd G):= by
    obtain ⟨d,he⟩:= WickFace.gap p H 1 0; have hv:d≠0:=fun h=> (sub_ne_zero.mpr ((show Injective p.val.ofLp from p.property).ne ( show (1:Fin 2)≠0 from by decide ))) ( he.trans (h ▸ zero_smul _ _)); rw [← PhaseTilt.tilt_two h M ν W' K S hs hr hu (-1), Equator.clocks ν M W' S h hs, show ν- (-1)=ν+1 from (by ring), adjust M ν l p S W' h hs d 1 hv he,Equator.before ]; simp only [one_mul, neg_mul ]
end
end YM.SignedWilsonExpansion.Overlap.Statement
