import YM.RG05Readout.Records.Dye
/-!
# Issue genuine upper crop. Price paid independently of number of replicas

General constructor; use for actual shaped upper product. Emits unnormalized
coarse sector polynomial in normalized master colors, with true fills. At n
output this polynomial still equivariant and the counter roots significant.
Color seams not needed in price estimate once occurrence constraints given.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records.Basket
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d ℓ:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D)
set_option quotPrecheck false
local notation "λ"=> C.path.levels.clock
local notation "R!"=> C.path.rep N p
local notation "Z!" => C.path.levels.budget
local notation "T"=> Recipe J V
local notation "L"=>Unit × Recipe J V
local notation "L'"=>Unit × Root J
local notation "Λ"=> basin J V
open Ribbons.ManyCopies
local notation "Π"=>partialGroup Unit (basin J V)
local notation "X!"=>C.side n p
local notation "J!"=> C.side N p
local notation "η"=> Ribbons.peepers C.path.levels n
section
variable {o:Unit×V→Site (C.side n p)} {s:Unit×V→ℕ}{E:Unit×V→Motion}{Q:ℝ}
    {X:(i:Unit×V)→Palette C (s i)} {P:(i:Unit×V)→Sight C (s i) p}{S:(i:Unit×V)→Emblems C (s i)}
    {Z:∀ i:ℕ,ManyStem C o i→Body} {B₀:Census (Unit×V)}{U:Census (Unit×I)} {f:Unit×V→ℂ}
variable (A:Ribbons.Fibers V I)(S':Finset I)
local notation "M"=> partialGroup Unit A
include h Y hC hS
lemma phaseOne (H:∀ i:Unit×V,Spine D B h n p (s i) N (P i) (S i)) (hn:0<n) (hk:n < m)(hm:m ≤ N)(ho:Occupancy o ((λ).J n))
    (hc:Clearance o E s Z B₀ m) (hp:PreparedA (Mine.tree o E) Z n N le_rfl) (hQ:∀ j: ManyStem C o n, Cap (s j.val.fst+2) (Z n j) 1)
    (hX:∀ i:Unit×V,size (X i) ≤ Q) (hy:0 < Q) (ht:Warm C n (d+1) k) (hs:∀ i:Unit×V,s i ≤ d)
    (hh:∀ i, ‖f i‖ ≤ 1)(hf:0<b)(hb:∀ i:Unit×I,((M).contents i).card ≤ b) (ha:∀ i∈S', A.Solo i)(hT: Pantry.Policy A B₀ U)(h_l:∀ i:Unit×V,coverNumber (Z! n).B ({(o ∘ (M).twig) ((M).bunch i),o i}:Support (C.side n p)) ≤ η):
    let z:=fee C m n d k b Q
    let Lx:= fun i:Unit×V=> clinic C p N (s i) (Launch (m:=m) s S X i N) n (o i) (E i) (Z n ((Mine.remap o E).symm i))
    let q:=birth U (R! N) (fun i Y'=>∏ j∈ (M).contents i,(f j+ Lx j Y'))
    let x:= (imprint h (Mine.tree o E) Z (plants (m:=m) s P S X) n (hk.le.trans hm)) ∘ (Mine.remap o E).symm
    0< z∧ Integrable q (prior G _) ∧ ∃ U':Unit×I→Three G X!, MenuBoard (R! n) U' (gust C.path N p N q n (hk.le.trans hm)) (o ∘ (M).twig) (fun _=>z) ((Z! n).supportExponent-2) 1 ∧ ∀ i:Unit×I, let j:=(M).twig i; (i.2∈S'→ U' i= stuff (x j) (R! n) (f j)) ∧ (i.2∉S'→ MergeProof.Float.Blade (R! n) (o j) ((U' i).snd.1) (profile ((R! n).activities) ((U' i).snd.2)) 0 (4*(1/z))):=by
     intro z L_k q x; let v:=Launch (m:=m) s S X; let a:=Mine.tree o E
     let F_N:=birth (Mine.ward o E B₀ N) (R! N) (fun i=>stepUp (a.motion (a.labelY N i)) (a.supportX N i) (entrance C (s (a.labelY N i)) N p (v (a.labelY N i) N) 0 (Z N i))); let he:= hk.trans_le hm
     obtain ⟨F',hr,hF⟩:=wind o E s he.le F_N
     obtain ⟨hw,J,hJ,hY⟩:=recompense o E s Z h Y hC hS P S X A f H hn hk hm ho hc hp hQ hX hy ht hs hF hr hh hf hb S' ha hT h_l
     obtain ⟨hy',hL⟩:= folded h he.le hF hr hp
     obtain ⟨ht',hK⟩:= brewed A f hT L_k he.le hy'
     refine ⟨hw,ht',J,?_,hY⟩; rw [show gust C.path N p N q n _= _ from hK]; have ht:gust C.path N p N (birth B₀ (R! N) L_k) n he.le= _:=hL; simp_rw [ht]; exact hJ
-- ?.simp_rw
end
section tune
variable (e:J→I)(c:J→Site (C.side n p))(E:J→Motion)(y:V→Site (C.side n p))(s:V→ℕ)(F:V→Body)(q:J→Body)
local notation "o"=> roads (C:=C) (n:=n) (p:=p) c E y
local notation "ℰ"=> side_E E (V:=V)
local notation "s!"=>toss s d (J:=J)
local notation "Ω"=> Mine.tree (o) (ℰ)
variable (f:Palette C d) (T':(j:V)→Palette C (s j))
variable (P: Sight C d p)(S: Emblems C d)(A:(j:V)→Sight C (s j) p)(U:(j:V)→Emblems C (s j))
local notation "Z"=> dye s d T' f (J:=J)
include S U in
def modeM (a:L): Emblems C (toss s d a):=by
   rcases a with ⟨⟨⟩,k,((( _|i))|⟨⟩)⟩
   · exact S
   · exact U i
   exact S
-- include?
include P A in
def visual (a:L): Sight C (toss s d a) p:=by
   rcases a with ⟨⟨⟩,k,((( _|i))|⟨⟩)⟩
   · exact P
   · exact A i
   exact P
local notation "SM"=>modeM s S U (J:=J)
local notation "V!"=>visual s P A (J:=J)
local notation "r!"=>  Many.point S f m
local notation "X₁"=> (fun j:V=> Many.point (U j) (T' j) m N)
-- Caps and bridges
omit [DecidableEq V] [Fintype V] [DecidableEq J] [Fintype J] in
lemma signing (_h:Spine D B h n p d N P S)(_ha:∀ i:V,Spine D B h n p (s i) N (A i) (U i)):∀ i:L,Spine D B h n p (s! i) N (V! i) (SM i):=by
    rintro ⟨⟨⟩,k,((_|i)|⟨⟩)⟩; exact _h; exact _ha i;exact _h
local notation "B₁"=>coats (C:=C) (n:=n) (p:=p) c E y F q
omit [DecidableEq V] [Fintype V] [DecidableEq J] [Fintype J] in
lemma crown (hv:∀ i:V,Cap (s i+2) (F i) 1) (hq:∀ i:J,Cap (d+2) (q i) 1)(j: ManyStem C o n) : Cap (toss s d (Ω|>.labelY n j)+2) (B₁ n j) 1:=by
    let e:=Mine.remap o ℰ; rcases e.symm.surjective j with ⟨a,rfl⟩; rw [show B₁ n (e.symm a)=_ from coats_link ..]; rcases a with ⟨_,k,((_|i)|⟨⟩)⟩
    exact (zero_basis _).increase zero_le_one; exact hv i; exact hq _
local notation "U₀"=> brisk e
local notation "d!"=> Fintype.card (Color V)
local notation "A₀"=> font e (V:=V)
variable {Q:ℝ}
include h Y hC hS
lemma shoot (hP:Spine D B h n p d N P S)(hA:∀ i:V,Spine D B h n p (s i) N (A i) (U i))
   (hn:0<n)(hk:n < m)(hm:m≤N)(hB:Occupancy (o) ((λ).J n))(hL:Clearance (o) (ℰ) (s!) (B₁) (A₀) m)(hv:∀ i:V,Cap (s i+2) (F i) 1)(hq:∀ i:J,Cap (d+2) (q i) 1)
   (hy:∀ i:V,size (T' i) ≤ Q)(hf:size f ≤ Q)(hQ:0 < Q) (ht:Warm C n (ℓ+1) k)(hg:∀ i,s i ≤ ℓ)(hd:d ≤ ℓ) (hh:∀ i:L,coverNumber (Z! n).B ({(o ∘ (Π).twig) ((Π).bunch i),o i}:Support X!) ≤ η) :
    let z:= fee C m n ℓ k d! Q
    let qx:=coarse_base c E y s F q (r! N) X₁ (hk.le.trans hm)
    let b:= birth U₀ (R! N) qx
    0<z∧ Integrable b (prior G _) ∧ ∃ X:L'→Three G X!, MenuBoard (R! n) X (gust C.path N p N b n (hk.le.trans hm)) (fun i=> c i.snd.fst) (fun _=>z) ((Z! n).supportExponent-2) 1 ∧ ∀ i:J,
          Signpost (R! n) (E i) (c i) ((P n (r! n)) (q i)) (X ((),i,false)) ∧ MergeProof.Float.Blade (R! n) (c i) ((X ((),i,true)).snd.1) (profile ((R! n).activities) ((X ((),i,true)).snd.2)) 0 (4*(1/z)):=by
   intro z qx bx; let I':=B₁
   have he:0 < Fintype.card (Color V):= Fintype.card_pos_iff.mpr ⟨Basket.center V⟩
   have hc(a:L): ‖pop V J a‖≤1:=by unfold pop; split<;> simp
   have hΓ(i:L):size (dye s d T' f i) ≤ Q:=by rcases i with ⟨⟨⟩,k,((_|i)|⟨⟩)⟩; exact (Address.size_zero (d:=d) (C:=C)).trans_le hQ.le; exact hy i;exact hf
   have hfee:∀ i:L,toss s d i ≤ ℓ:=by rintro ⟨⟨⟩,k,((_|i)|⟨⟩)⟩; exact hd; exact hg i;exact hd
   have hy': PreparedA Ω (coats c E y F q) n N le_rfl:= (Many.headlines ..).2
   obtain ⟨hξ,hX,q',hr,hG⟩:= phaseOne h Y hC hS (basin J V) (back J) (signing h s P S A U hP hA) hn hk hm hB hL hy' (crown c E y s F q hv hq) hΓ hQ ht hfee hc he basin_count (plain (V:=V)) (pilot_paid e) hh
   let V₀:= fun a:L => clinic C p N (s! a) (Launch (m:=m) s! SM Z a N) n (o a) (ℰ a) (B₁ n ((Mine.remap o ℰ).symm a))
   have hΔ: qx=fun i X=> ∏ a∈ Π.contents i,(pop _ _ a+ V₀ a X):=by
       funext i X; apply Eq.trans (lays c E y s F q (r! N) X₁ (hk.le.trans hm) i X).symm; apply prod_congr rfl; intro a _; unfold V₀; rw [show B₁ n _=_ from coats_link c E y F q a]
       rcases a with ⟨⟨⟩,k,((_|i)|⟨⟩)⟩; rotate_left; rfl; rfl
       congr 3 -- for 0 map.point
       change clinic C p N d 0 n _ _ _ _=clinic C p N d (Many.point S 0 m N) n _ _ _ _; rw [weave_fine hm,map_zero]
   have hU: o ∘ Π.twig = fun i=> c i.snd.fst:=by funext i; rcases i with ⟨⟨⟩,i,p⟩; cases p<;> rfl
   unfold bx; rw [hΔ]; refine ⟨hξ,hX,q',hU ▸ hr,?_⟩; intro i; refine ⟨?_, (hG ((),i,true)).2 ?_⟩; rotate_left; · simp [back]
   rw [(hG ((),i,false)).1 (by simp [back]),show pop V J (Π.twig ((),i,false))=0 from if_neg (by dsimp [partialGroup,basin]; intro h; cases h),spice_right]
   let j:=(Mine.remap o ℰ).symm ((),i,counter V); have he': I' n j=q i:=coats_link ..
   rw [← he']; apply View.spin_at
end tune
end YM.RG05Readout.Records.Basket
