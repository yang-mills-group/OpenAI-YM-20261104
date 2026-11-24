import YM.SignedWilsonExpansion.PhaseTilt
namespace YM.SignedWilsonExpansion.PairWave
/-! Pairs in ordinary arrays v. connected values. Evaluate log by the
 very `Puff.Mom.bouquet` stories, matched-continuum (same projection). -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Plane MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land MS.Puff MS.Puff.Mom MS.Puff.SplitP MS.Puff.Engine MS.Puff.Actors
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace PhaseTilt
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O) (ν:ℝ) {n:ℕ}
local notation "v" => Press.portDeck G
local notation "Q" => (PowerSeries ℂ)
local notation "Ψ" => Equator.wave ν M 4
abbrev grade2 (G:Gauge):= MarkRows.I (Press.portDeck G)
local notation "ι" => grade2 G
local notation "ζ" => (fun i:ι=> Land.read (MarkRows.address i))
local notation "C" => Sec G 4
local notation "E" => WickFace.lens G
local notation "γ" => Energy.called 1 2 G
abbrev kind (i:grade2 G) := Dframe.theory (Land.read (MarkRows.address i)) -- Inferred grade.
lemma coerces : E=∑ i:grade2 G, (γ i:ℂ) • (kind i):= by
   let b:= Theater.Resume v 4 2; let r:=Energy.here 1 2 G; have hp:( Theater.Resume v 4 2 r ).val=Energy.off 1 2 G:= by
      let v': Film0 G 4 2:= ⟨Energy.off 1 2 G,Energy.admitted 1 2⟩;  refine congr_arg (fun a:Film0 G 4 2=> a.val) (?_ : Theater.Resume v 4 2 r=v'); exact ( Theater.craftK G 4 2 ).injective ( Subtype.ext ( ( honor v r ).trans ( Energy.over_color _ _ ).symm ) )
   apply Subtype.ext; obtain he:= ( Module.finBasis ℝ _ ).sum_repr r
   rw [ blaze, show Energy.raw G 1 2=reduceEq ( Theater.Resume v 4 2 r ).val from (by rw [ hp, ← Energy.sectionE ]; exact ( On.lift_recover _ ).symm ), ← he, map_sum ]; simp_rw [map_smul]; -- factor real-union
   let T:Film0 G 4 2→ₗ[ℝ] WickPol G:= stageM G 4 2; change T (∑ i:ι, γ i • Theater.Resume v 4 2 (( Module.finBasis ℝ _ ) i) ) = _; rw [ map_sum, AddSubmonoidClass.coe_finsetSum ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ map_smul ]; change γ i • ( ( kind i ).val )=( (γ i:ℂ) ) • ((kind i).val); exact (IsScalarTower.algebraMap_smul ℂ (γ i) (kind i).val ).symm
section Puff
variable (S: Finset (Fin n)→(ℕ→ℂ)) (he:S ∅=0)(W:Finset (Fin n))
local notation "A" => Trunk.stack ( marked (Fin n) )
lemma zeroL (h:W.Nonempty) : ((Trunk.stack ( marked (Fin n) )).wages S 0) W=0:= by unfold wages Actors.power; have he: (A).unit W=0:=if_neg ( Finset.nonempty_iff_ne_empty.mp h ); rw [Pi.smul_apply, he, smul_zero]
lemma turnOne : ( Trunk.stack (marked (Fin n))).power S 1 = S := (Trunk.stack ( marked (Fin n))).identityR _
lemma equip (i:Fin n): Mom.bouquet S {i}= S {i}:= by
   unfold Mom.bouquet Actors.Cheer; change (( Trunk.stack ( marked (Fin n) ) ).cheers S ( Finset.card ({i}:Finset (Fin n)) )) {i}=_; rw [ Finset.card_singleton,cheers, show Finset.range (1+1) = {(0:ℕ),1} from rfl, sum_pair (by decide), Pi.add_apply,zeroL _ _ ( Finset.singleton_nonempty _ ), zero_add ]; unfold wages; rw [turnOne]; simp [phase]
lemma biphase (x y:(ℕ→ℂ)) (n:ℕ) : Trunk.core x y n= ∑ j∈Finset.antidiagonal n,x j.1*y j.2:=rfl
private lemma cardp : ( univ : Finset (Fin 2) ).card=2:=rfl
lemma pair_b {S: Finset (Fin 2)→(ℕ→ℂ)} (h:S ∅=0):
     Mom.bouquet S (univ:Finset (Fin 2))= S univ+Trunk.core ( S {0} ) ( S {1} ):= by
   let A':= Trunk.stack ( marked (Fin 2) ); let P:=A'.power S
   unfold Mom.bouquet Actors.Cheer; change A'.cheers S ( univ:Finset (Fin 2)).card univ=_; rw [cardp, cheers, show Finset.range (2+1)= {0,1,2} from rfl, sum_insert (by decide),sum_pair (by decide),Pi.add_apply, Pi.add_apply, zeroL S univ univ_nonempty,zero_add ]; unfold wages
   have ht : A'.power S 2 univ=(2:ℂ) • Trunk.core ( S {0} ) ( S {1} ) := by
       rw [ Actors.power, turnOne S ]; change ∑ j∈subs (univ:Finset (Fin 2)),Trunk.core ( S j.1 ) ( S j.2 ) = _; rw [ show SplitP.subs (univ:Finset (Fin 2))={(∅,Finset.univ),(Finset.univ,∅),({0},{1}),({1},{0})} from by decide ] ; simp (disch:=decide) only [ h,map_zero, LinearMap.zero_apply, Finset.sum_insert,Finset.sum_singleton,zero_add ]; -- symmetry both.Develop
       rw [← Trunk.turns ( S {0} ) ?_ ( S {1} ) ?_, two_smul]; all_goals exact fun _ _=> Submodule.mem_top
   rw [ turnOne S ]; simp only [ Pi.smul_apply, ht ]; norm_num [phase, Nat.factorial]; module -- budget field calc
end Puff
local notation "W" => (Finset.univ (α:=Fin 2))
local notation "K" => (Finset.univ (α:=Fin 1))
variable (x:Stage n)
local notation "kY" => Arrival.Schedule.plot
local notation "xQ" => kY x.val
variable (w:Fin n→Toon G 4)
local notation "Y₀" => Dial.book M
lemma emptyB : Dial.book M ( Dframe.flash ∘ w ) ν ( kY x.val ) ∅=0:= by
    obtain h:= Dial.pin M ( Dframe.flash ∘ w ) ν ( Arrival.Schedule.track x.property ); funext i; unfold Dial.book; rw [ h.1 ]; exact ( Fleet.allow_zero ( I:=Unit ) ()|>.2 )
-- isolated marks independent
variable (y:Stage 1)
def mon (i:ι)(z:ℝ) : (ℕ→ℂ):= Dial.book M (fun (_:Fin 1)=> Dframe.flash (Land.read (MarkRows.address i))) z ( Arrival.Schedule.plot y.val ) {0}
lemma solo_book (i:Fin n)(j:ι)(hh:w i=ζ j) : Dial.book M ( Dframe.flash ∘ w ) ν (kY x.val) {i}=mon M y j ν:= by
   have he:= Dial.pin M ( Dframe.flash ∘ w ) ν (Schedule.track x.property); have hr:= Dial.pin M (fun (_:Fin 1)=> Dframe.flash (ζ j)) ν (Schedule.track y.property)
   funext n; unfold mon Dial.book; rw [ he.2.1, hr.2.1 ]; simp_rw [ Function.comp_apply, hh ] -- namespace
abbrev sd (G:Gauge): Tags G 4 1:= fun _=> WickFace.lens G
abbrev dd (G:Gauge): Tags G 4 2:= fun _=> WickFace.lens G
lemma moment_s (t:ℕ): Equator.wave ν M 4 1 y t (sd G)=∑ j:ι, (γ j:ℂ)*mon M y j ν t:= by
    let P:Module.Dual ℂ (Sec G 4):=(Ψ 1 y t).toLinearMap (sd G) 0; rw [ show Ψ 1 y t (sd G)=P E from ?_, coerces, map_sum ]; swap; · apply congr_arg (Ψ 1 y t); exact (update_eq_self ..).symm
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [ _root_.map_smul ]; let w: Fin 1→Toon G 4:=fun _=> ζ i; have h:update (sd G) 0 (kind i)=Dframe.fill w:= funext fun k=> (by fin_cases k; simp only [Function.update_self]; rfl)
    rw [ show P ( kind i )=_ from ( congr_arg (Ψ 1 y t) h ),Equator.wave,ribbon ]; unfold continuum Landing.moondye Dial.tour; rw [ show K={0} from rfl, equip ]; rfl
section twin
variable (p:Stage 2)(t:ℕ)
private lemma o0 (x:Stage 1): Ψ 1 x 0 (sd G)=0:= by
    rw [ before ]; refine Eq.trans ?_ ( WickFace.single_off (G:=G) x (0:Fin 1) 3 3 ); apply congr_arg ( Maxwell.Wick.moment G x.val ); funext i; fin_cases i; simp only [update_self]; rfl
abbrev duo_t (i j:grade2 G): Fin 2→ Toon G 4:=![ Land.read ( MarkRows.address i ), Land.read ( MarkRows.address j ) ]
lemma ledger (t:ℕ)(i j:grade2 G) : Ψ 2 p t ( Dframe.fill ( duo_t i j ) )=
      Dial.book M (PhasePair.roster i j) ν ( kY p.val ) (univ:Finset (Fin 2)) t+ (Trunk.core ( mon M y i ν ) ( mon M y j ν )) t:= by
    unfold Equator.wave; rw [ribbon]; unfold continuum Landing.moondye Dial.tour; rw [ pair_b ( emptyB M ν p ( duo_t i j ) ), Pi.add_apply, solo_book M ν p _ y 0 i rfl, solo_book M ν p _ y 1 j rfl ]; have he: Dframe.flash ∘ duo_t i j= PhasePair.roster i j:=by funext i; fin_cases i <;> rfl
    rw [he]
lemma wage (t:ℕ): Ψ 2 p t (dd G)= PhasePair.sale_at M ( kY p.val ) ν t + Trunk.core ( fun t=> Ψ 1 y t (sd G) ) (fun t=> Ψ 1 y t (sd G) ) t:= by
    let A0:= Ψ 2 p t; let U:= dd G; have he : A0 U=∑ i:grade2 G,∑ j:grade2 G, (γ i:ℂ)*(γ j:ℂ)*A0 ( Dframe.fill ( duo_t i j ) ):= by
       let W'(i:grade2 G):= update U 0 (kind i); let P:=A0.toLinearMap U 0
       rw [ show A0 U=P E from ?_, coerces,map_sum ]; swap; · exact ( congr_arg A0 (update_eq_self ..) ).symm
       apply Finset.sum_congr rfl; intro i _; rw [ _root_.map_smul ]; let Q':=A0.toLinearMap ( W' i ) 1
       rw [ show P (kind i)=Q' E from ?_,coerces,map_sum, Finset.smul_sum ]; swap; · apply congr_arg A0; rw [← show W' i 1=E from (by unfold W'; simp [dd,U]) ]; exact (update_eq_self ..).symm
       apply Finset.sum_congr rfl; intro j _; rw [ map_smul ]; rw [show Q' (kind j)= A0 (Dframe.fill ( duo_t i j )) from (by apply congr_arg A0; funext i; fin_cases i <;> first| rfl| simp only [ Function.update_self,Function.update_of_ne (by decide : (0:Fin 2)≠1) ]; rfl ), smul_eq_mul,smul_eq_mul ]; ring
    change A0 U= _; rw [he]; unfold PhasePair.sale_at; unfold A0; simp_rw [ ledger M ν y p ]; -- need ∑̊ linear
    have hz: (fun t=> Ψ 1 y t (sd G))=∑ i:ι, (γ i:ℂ) • mon M y i ν:= by funext t; rw [ moment_s M ν y t, Finset.sum_apply ]; rfl
    -- casts
    rw [ hz ]; simp_rw [ mul_add,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.sum_apply,Finset.sum_add_distrib, Pi.smul_apply ]; -- order?
    congr 1; rw [ Finset.sum_comm ]; -- check comm swapped
    exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by simp only [ smul_eq_mul ]; ring
include y in
lemma pair_price : Ψ 2 p 0 (dd G)= PhasePair.sale_at M ( kY p.val ) ν 0:= by rw [ wage M ν y p, biphase ]; simp [o0]
-- order1 zero both.sweep
variable (S: Land.Prescription (Press.portDeck G))(W':Initialize G)(simple:G.Simple)(hp:TaylorOKF M (Press.wickInput W') S)
include hp simple
include y in
lemma high_price : Ψ 2 p 2 (dd G)=PhasePair.sale_at M ( kY p.val ) ν 2:= by
    rw [ wage M ν y p,biphase ]; have ht:Ψ 1 y 1=0:= PhaseTilt.parity_point simple _ (FVA2.Parity.Invol.earns ν W' S M simple hp ( d:=4 ) y.property); rw [show Finset.antidiagonal 2={(0,2),(1,1),(2,0)} from by decide,sum_insert (by decide),sum_insert (by decide),sum_singleton ]; rw [ o0 M ν y,zero_mul,mul_zero, ht ]; simp
lemma charged (d v0:ℝ)(h:d≠0)(he:p.val 1-p.val 0=timeLine d):
    Ψ 2 p 2 (dd G)- Equator.wave (ν+v0) M 4 2 p 2 (dd G)= ((-2*( v0*OrderHigh.kinetic G + v0*OrderHigh.locus G)):ℝ ) • (Ψ 2 p 0 (dd G)):= by
    let q:= kY p.val; have hu : q 1-q 0= FourierGaussian.axis d:= by
       rw [ show q 1-q 0 = Theater.out (timeLine d) from (by rw [← he]; exact (_root_.map_sub ..).symm) ]; unfold timeLine FourierGaussian.axis; rw [ map_smul ]; rfl
    -- can any y for price
    let y : Stage 1:=⟨ 0, fun _ _ _=> Subsingleton.elim ..⟩
    rw [high_price M ν y p S W' simple hp, high_price M _ y p S W' simple hp,pair_price M ν y p, ← neg_sub ( a:=PhasePair.sale_at M q (ν+v0) 2 ), PairFlow.delta_end M simple q h (Schedule.track p.property) hu ]; simp only [ neg_mul,neg_smul,q ]
end twin
end
end YM.SignedWilsonExpansion.PairWave
