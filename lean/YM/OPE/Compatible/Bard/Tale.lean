import YM.OPE.Compatible.Bard.Rock
/-! Copy interpretation of cove vs remaining. Holds for both types. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells
open scoped Topology BigOperators Classical
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k i s J:ℕ}
variable (P:Wave m U K i)(P':Wave m K F s)(x:brim D F)(hv:x.val ∈ brim D K)
set_option quotPrecheck false
local notation "I₀"=> (C.labels.level d).Index
-- counterterm actual units. need Budget in S stage
variable (L:Extra.Histories.Music (C.labels.level d) C.path N p)(v:C.label d)
local notation "D!"=> C.factory d N p
local notation "X'"=> (D!).terminal v
lemma submit (k:ℕ) (o:Site (C.S.side N p)) : (∑ i:I₀, -((L.tone k).index v i) • C.O N p (lyric C L k i) o) = - C.O N p ((C.factory d N p).terminal v) o:=by
    let A := (L.tone k).index; have he : ∑ i:I₀,(A v i) • sonnet C L k i=v:=by
       apply A.injective; rw [map_sum]; simp_rw [map_smul,sonnet]; change ∑ i:I₀, (A v i) • A (A.symm _)= _; simp_rw [LinearEquiv.apply_symm_apply,Size.sum_axes]
    have hh: ∑ i:I₀,(A v i) • C.O N p (lyric C L k i) o= C.O N p ((C.factory d N p).terminal v) o:=by
       let F:= (C.linearO N p d o).mk' _; nth_rw 2 [← he] -- uses in weighted LHS? `v` appears first A v i then termine
       change _ = F _; rw [map_sum,map_sum]; apply sum_congr rfl; intro i _; rw [map_smul,map_smul]; rfl
    simp_rw [neg_smul,sum_neg_distrib]; exact congr_arg (- ·) hh
variable (q: brim D U→ℕ)(Q:∀ i,C.label (q i))
    (O:X→Track C.path T p) (E:Ensemble T) -- relative O around xK. assume affine transforms across p
set_option quotPrecheck false
-- Y starts with actual
local notation "x'"=> (⟨x.val,hv⟩:brim D K)
def entered(Q:∀ i:brim D U,C.label (q i))(O:X→Track C.path T p)(E:Ensemble T) (x:X)(L:Extra.Histories.Music (C.labels.level d) C.path N p)(k:ℕ)
    (i: T×(brim D U⊕ (C.labels.level d).Index)) : Config G (C.S.side N p)→ℂ:=i.2.elim (fun j=>stepUp (E.move i.1) (O j.val N i.1) (C.O N p (Q j) 0)) (fun j=>stepUp (E.move i.1) (O x N i.1) (C.O N p (lyric C L k j) 0))
-- inspect order args or issues: D shadow
local notation "X0" => entered D q Q O E x.val L k
local notation "c" => -(L.tone k).index v
local notation "f!" => Deb.portion (atopBy T (foldTo (W:=I₀) x)) (spices E (dyes (I:=brim D F) c)) (spurs D (spurs D X0 P) P')
def shop(Y:∀ i:brim D U,C.label (q i))(x:X)(A: X→ Site (C.side N p))(t:C.label d): Config G (C.side N p)→ℂ:= (∏ i∈ cove D U x, C.O N p (Y i) (A i.val))- C.O N p t (A x)
def peers(Y:∀ i:brim D U,C.label (q i))(x:X)(A:X→ Site (C.side N p)) := ∏ i∈ univ\ cove D U x,C.O N p (Y i) (A i.val)
section
variable (A:X→ Site (C.side N p))(hC:C.Makes) (hk:J ≤ N)
    (j0: Site (C.side J p)) (y:T) (he:E.move y= hands C p J j0)
    (h:∀ i∈allUp D U,O i N y=affine (E.move y).1 (Mix.camp C p J N j0) (A i))
local notation "T0"=> center C.S p hk 0
include hC h hk he E
omit [Fintype T][DecidableEq T] in
lemma seen_live {w:ℕ}{i:X}(hi:i∈allUp D U)(b:C.label w): stepUp (E.move y) (O i N y) (C.O N p b 0) = (center C.S p hk 0).copy j0 (C.O N p b (A i)):=by
    rw [← handmove C N p J hk, h _ hi,he, ← show stepUp (1,false) (A i) (C.O N p b 0)=C.O N p b (A i) from itemT C N p w hC b _] -- rw inside LHS maybe loop
    rw [flyF]
omit hC h he E D
include P
omit P [PartialOrder X][Fintype X][OrderBot X] in
lemma copies_product (x:X→ Config G (C.S.side N p)→ℂ)(S:Finset X) : (T0).copy j0 (∏ i∈S,x i)=∏ i∈ S,(T0).copy j0 (x i):=by
    funext s; unfold Tiling.copy; split_ifs <;> first|simpa only [prod_apply,star_prod]|simp  -- needs eq rearr after split
-- because varied index param
include hC h he E D P P' hv
set_option maxHeartbeats 200000 in
lemma speak_cost (hX : x.val∈allUp D U) : (f!) (y,x)=(T0).copy j0 (shop D q Q x.val A ((C.factory d N p).terminal v))∧ ∏ i∈univ.erase x,(f!) (y,i)=(T0).copy j0 (peers D q Q x.val A):=by
    let t:=entered D q Q O E x.val L k; let Y:=spurs D t P; let Z:=spurs D Y P'; let z:= c; let u:=fun i:brim D U=>C.O N p (Q i) (A i.val); let W:= center C.S p hk 0
    have ht(i:brim D U): t (y,.inl i)= W.copy j0 (u i):= seen_live D O E A hC hk j0 y he h (mem_union_right _ i.2) _
    have hr(i:I₀):t (y,.inr i)=W.copy j0 (C.O N p (lyric C L k i) (A x.val)):= seen_live D O E A hC hk j0 y he h hX _
    let v' := (⟨x.val,hv⟩:brim D K); have hp':Y (y,.inl v')=W.copy j0 (∏ j∈ cove D U x.val,u j):=by
       unfold Y; rw [spur_node,elements_bunch]; simp_rw [ht]; rw [copies_product] -- params
    have hf: Z (y,.inl x)=Y (y,.inl v'):=by unfold Z; rw [spur_node,singleton_later D P' x v' rfl,prod_singleton]
    have hg(i:I₀): Z (y,.inr i)=t (y,.inr i):= ((spur_extra D P' Y y i)).trans (spur_extra D P t y i)
    constructor
    · rw [branching,if_pos rfl]; unfold shop; change Z (y,Sum.inl x)+_=W.copy j0 _; rw [hf,hp']
      let p':=C.factory d N p; let Y' i:=C.O N p (lyric C L k i) (A x.val); have hK:(fun b : Config G (C.S.side N p)→ℂ=> W.copy j0 b)=(fun b=>stepUp (E.move y) (Mix.camp C p J N j0) b):= funext fun i=>by rw [he,handmove C N p J hk]
      have hL : ∑ i:I₀,E.echo (z i) y • Z (y,.inr i)=W.copy j0 (- C.O N p (p'.terminal v) (A x.val)):=by
          rw [← show ∑ i:I₀,z i • Y' i= - _ from submit ..]; simp_rw [hg,hr]; let T:= Mix.camp C p J N j0
          funext i; rw [Finset.sum_apply]; unfold Ensemble.echo; have hY(i:Config G (C.S.side N p)→ℂ): W.copy j0 i=stepUp (E.move y) T i:=congr_fun hK i; simp_rw [hY]
          unfold stepUp; simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,pipes, Motion.scalar_mul]; rfl
      change W.copy j0 _+(∑ i:I₀,E.echo (z i) y • Z (y,.inr i))=W.copy j0 _; rw [hL, sub_eq_add_neg]; funext i; unfold Tiling.copy; split_ifs <;> simp only [Pi.add_apply,star_add] <;> first|rfl -- need definitional shapes
    calc
       _ = ∏ i∈univ.erase x,∏ j∈ (elements D P').contents i,Y (y,.inl j) := Finset.prod_congr rfl fun i hi=> by rw [branching,if_neg (Finset.mem_erase.mp hi|>.1),add_zero]; exact spur_node D P' Y y i
       _ = ∏ i∈ univ.erase v', Y (y,.inl i):= by rw [besides_cove]; rw [← elements_bunch D P',singleton_later D P' x v' rfl,sdiff_singleton_eq_erase]
       _ = ∏ i∈univ.erase v',∏ j∈(elements D P).contents i,(T0).copy j0 (u j):= Finset.prod_congr rfl fun i _=> (spur_node D P t _ i).trans (prod_congr rfl fun j _=> ht j)
       _ = _ := by unfold peers; rw [besides_cove, copies_product]
end
end YM.OPE.Arboreal.Arcade
