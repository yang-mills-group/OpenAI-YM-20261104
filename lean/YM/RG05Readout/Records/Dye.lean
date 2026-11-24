import YM.RG05Readout.Records.Button
/-!
# Authentic product computation for one anchored signed family

Sources are tagged as `Recipe`, use hats at N before issuing transcript.
Summation / test pulls tied to that density, profile paid all admissible groups.
Counter product steering not inferred from price at positive slots; priced by
parallel branch. All at finite C. Works for actual motions INCLUDING wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records.Basket
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
set_option quotPrecheck false
local notation "R₀"=> C.path.rep N p N
local notation "T"=> Recipe J V
local notation "Λ"=> basin J V
open Ribbons.ManyCopies
local notation "L"=>Unit × Recipe J V
local notation "L'"=>Unit × Root J
local notation "T!"=> Color V
local notation "Π"=>partialGroup Unit (basin J V)
local notation "Z!"=> C.side N p
lemma zero_basis (d:ℕ): Cap d 0 0:=by intro i hi x hx; change ‖iteratedFDeriv ℝ i (0:E4→ℂ) x‖≤0; simp
variable (c:J→Site (C.side n p)) (E:J→Motion)(y:V→Site (C.side n p)) (s:V→ℕ)(F:V→Body) (q:J→ Body)
def toss (s:V→ℕ)(d:ℕ)(a:Unit × Recipe J V):ℕ:=match a.snd.snd with | Sum.inl (some i)=> s i | _=> d
abbrev roads (a:L):Site (C.side n p) :=match a.snd.snd with | Sum.inl (some i)=> affine (E a.snd.fst).1 (c a.snd.fst) (y i)| _=> c a.snd.fst
abbrev side_E (E:J→Motion)(a:L):Motion:= E a.2.1
def windF (a:L):Body:= match a.snd.snd with | Sum.inl (some i)=> F i | Sum.inr _=> q a.2.fst| Sum.inl none=> 0
local notation "o"=> roads c E y
local notation "M!"=> side_E E (V:=V)
local notation "U"=> toss s d (J:=J)
local notation "A"=> Mine.tree (o) (M!)
local notation "Λ!"=> (A).labelY
local notation "R"=> ManyStem C o
def coats (i:ℕ): R i→Body:= headings o M! (windF F q ∘ Λ! n) i
local notation "I!"=> coats c E y F q
omit [DecidableEq J] [Fintype J] [Fintype V] [DecidableEq V] in
lemma coats_link (i:L): let j:=(Mine.remap (o) (M!)).symm i; I! n j=windF F q i:=by
   intro j; unfold coats; rw [(Many.headlines (N:=0) ..).1]; rfl
lemma wedge (d:ℕ)(z: Palette C d)(h:n ≤ N):crops C N p N d le_rfl (precinct C p N d z) n h 0=0 :=by -- binder illegal
   induction h using Nat.decreasingInduction with
   | self=> rw [crops_head]; exact unlit _ _ _ _ _ (zero_basis _)
   | of_succ i hi ih=>
       rw [crops_step _ _ hi]; unfold replenishes; apply sum_eq_zero; intro j _; rw [map_zero,ih]; have hp :∀ n:Side,∀ y0:Site n,stepUp (1,false) y0 (0:Goods G n)=0:= fun _ _=> rfl; rw [hp,smul_zero]
-- top gain products
variable (M:Palette C d) (B:(i:V)→Palette C (s i))
def dye (s:V→ℕ)(d:ℕ) (B:(i:V)→Palette C (s i))(x:Palette C d)(a:Unit × Recipe J V):Palette C (toss s d a):= by
   rcases a with ⟨_,k,(((_|i))|⟨⟩)⟩
   · exact 0
   · exact B i
   exact x
local notation "Q!"=> dye s d B M (J:=J)

-- bare-vac standardized top direction choice; equivalent to shipping any lecture S with tally cap
lemma folded {e:I→Site (C.side n p)}{E':I→Motion} {u:I→ℕ}{W':∀ j,ManyStem C e j→Body} (h:C.Makes) {B':Census I}{f:∀ i:ℕ, Config G (C.side i p)→Poly (Mine.ward e E' B' i)}
   (ht:n ≤ N) {v:(i:I)→ℕ→Palette C (u i)} 
   (hp:f N=birth (Mine.ward e E' B' N) (R₀) (fun i:ManyStem C e N=> stepUp (Mine.tree e E'|>.motion ((Mine.tree e E').labelY N i)) ((Mine.tree e E').supportX N i) (entrance C (u ((Mine.tree e E').labelY N i)) N p (v ((Mine.tree e E').labelY N i) N) 0 (W' N i)))) (hr: Replay (Mine.tree e E') u (le_refl n) N f N)
    (hf': PreparedA (Mine.tree e E') W' n N le_rfl) :
    let g := fun i:I=> clinic C p N (u i) (v i N) n (e i) (E' i) (W' n ((Mine.remap e E').symm i))
   let C₀:= birth B' (R₀) g
   Integrable C₀ (prior G _) ∧ gust C.path N p N C₀ n ht=fun X=> baseFold e E' B' (f n X):=by
    intro g X; let T':=swell (le_refl N) (Mine.tree e E') u (fun j=>precinct C p N (u j) (v j N)) (W')
    have ht' : f N=birth (Mine.ward e E' B' N) (R₀) (T' N):=by rw [hp]; unfold T'; congr 1; funext i; rw [staples]
    have hs: Integrable (f N) (prior G _):=by rw [hp]; apply seen_top _ _ _ h
    rw [ht'] at hs
    obtain ⟨he,hΦ⟩:= reimburses (Mine.tree e E') u (le_refl N) T' (le_refl n) hr (fun i hi h' => pillar _ _ _ _ hi h' (hf' i hi h')) (by rw [gust_base,ht']) hs le_rfl ht
    rw [hΦ]
    let l:= Many.combine ((Mine.tree e E').labelY n) (W:=I) (fun _=>1) (T' n); have hh:l=g:=by
       funext i; unfold l Many.combine; let a':=(Mine.remap e E'); rw [Finset.sum_eq_single (a'.symm i)]; rotate_left
       · intro j _ hp; simp only [if_neg (show ¬(Mine.tree e E').labelY n j=i from fun h=>hp (a'.injective (h.trans (a'.apply_symm_apply _).symm))),zero_smul]
       · simp
       rw [if_pos (show (Mine.tree e E').labelY n (a'.symm i)=i from rfl),one_smul]; rfl
    unfold X; rw [← hh]; exact blended _ _ (Many.chamber B' ((Mine.tree e E').labelY n)) ht he

def pop (V J:Type)(a: Unit×Recipe J V):ℂ:= if a.snd.snd=Basket.center V then 1 else 0
local notation "V!"=>fun i:L=> clinic C p N (U i) (Q! i) n (o i) (M! i) (windF F q i)
local notation "ξ"=>pop V J

def bunchG : Goods G (C.side N p):= fun X=> ∏ i:V, clinic C p N (s i) (B i) n (y i) (1,false) (F i) X
-- populate fares
lemma culms (i:J) : Π.contents ((),i,true) = Finset.univ.image (fun q:Option V=>((),i,Sum.inl q)):=by
    ext s; rcases s with ⟨⟨⟩,j,v|⟨⟩⟩
    · rw [Ribbons.Fibers.focuses,Finset.mem_image]; constructor
      · intro h; exact ⟨_,Finset.mem_univ _,Prod.ext rfl (Prod.ext (congr_arg (fun i:L'=> i.snd.fst) h).symm rfl)⟩
      rintro ⟨k,-,hK⟩; rw [←hK]; rfl
    rw [Ribbons.Fibers.focuses,Finset.mem_image]; constructor
    · intro h; exact False.elim (Bool.noConfusion (congr_arg (fun i:L'=>i.snd.snd) h))
    rintro ⟨k,-,h⟩; cases h
local notation "Θ"=> C.S.toDepth
variable (ht:n ≤ N)
local notation "W!"=>fun j:J=> stepUp (E j) ((Θ ht p).embed (c j))
def coarse_base (i:Unit× Root J): Goods G (C.side N p) := if i.2.2 then W! i.2.1 (bunchG (C:=C) y s F B) else clinic C p N d M n (c i.2.1) (E i.2.1) (q i.2.1)
-- exact two branches
lemma lays (i:Unit×Root J)(X:Config G (C.side N p)) : ∏ j∈ (Π).contents i,(ξ j+ V! j X)=coarse_base c E y s F q M B ht i X:=by
   rcases i with ⟨⟨⟩,j,h⟩; unfold coarse_base; cases h
   · rw [if_neg Bool.false_ne_true,show Π.contents ((),j,false)={ ((),j,counter V)} from (Muster.crewed _ (back J) (fun i hi=> plain i hi) ((),j,false) ?_).content]; swap
     · simp [Ribbons.ManyCopies.Muster.crew,back] -- lookup
     rw [Finset.prod_singleton,show (ξ) ((),j,counter V)=0 from if_neg (by unfold counter center; intro h; cases h),zero_add]; rfl
   rw [if_pos rfl,culms, prod_image]; swap
   · exact fun i _ k _ h=>Sum.inl.inj (congr_arg (fun i:L=>i.snd.snd) h)
   rw [Fintype.prod_option]; let k:L := ((),j,Basket.center V)
   have he : ξ k+ V! k X=1:=by
      dsimp only; rw [show ξ k=1 from if_pos rfl]; unfold clinic uniform; rw [dif_pos ht]; change 1+ stepUp _ _ (crops C N p N _ le_rfl _ n ht 0) X=1;rw [wedge]; change 1+ Motion.scalar _ 0=1; rw [scalar_z,add_zero]
   rw [he,one_mul]; unfold bunchG stepUp; let t:= E j; let v:= (Θ ht p).embed (c j)
   have hT(t:Motion)(f:V→ℂ): Motion.scalar t (∏ i:V,f i)= ∏ i:V,Motion.scalar t (f i):=by unfold Motion.scalar;split; exact star_prod ..;rfl
   dsimp only; rw [hT]; refine prod_congr rfl fun a _=>?_
   let i:L:=((),j,producer a); rw [show ξ ((),j,producer a)=0 from if_neg (by unfold producer center; intro h; cases h),zero_add]
   change clinic C p N (s a) (B a) n (affine t.fst (c j) (y a)) t (F a) X= stepUp t v (clinic C p N (s a) (B a) n (y a) (1,false) (F a)) X
   unfold clinic uniform; simp_rw [dif_pos ht]; exact congr_fun (stair_rot ..).symm X
end YM.RG05Readout.Records.Basket
