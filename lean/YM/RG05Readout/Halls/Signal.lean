import YM.RG05Readout.Halls.Forms
/-!
# Supply Campaign. Universal roots and storyline Signature

Reservations can be lifted arbitrarily by positive additional Q when paying
for signed response. Derive Marker support from Cartesian finite demand:
all orientations and alternatives at old cells, unit normalized & priced from
master. Supply ANY Signature to consumers using exact physical Tag tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion Cells
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g ℓ t:ℕ}
set_option quotPrecheck false
local notation "Θ"=> C.path.levels
local notation "S'"=> C.S
local notation "Πξ"=> C.S.toDepth
local notation "K"=> C.path.levels.clock.op
local notation "α"=> C.S.a
local notation "G!"=> C.S.gridPoint
local notation "λ!"=> C.side
local notation "ω"=> Lattice.wrap
local notation "Z!"=>C.path.levels.budget
local notation "χ"=> (C.S.radius p)
local notation "X!"=> C.side n p
local notation "J!"=> C.side N p
local notation "P!"=> C.side b p
local notation "ξ"=> n+1
local notation "X₀"=> C.side (n+1) p
section
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D) (s:V→ℕ)(u: V→ Cover)(F:V→Body)
local notation "o"=> (fun j:V=> Lattice.wrap (C.side (n+1) p) (u j))
structure Knock (b n m p k d ℓ t:ℕ)(r a:ℝ)(C:Family G)(s:V→ℕ)(u: V→ Cover) (F:V→Body): Prop where
    level : b ≤ n
    east : n+1 < m
    cues (i:V) : ‖C.S.gridPoint (n+1) (u i)‖ ≤ a*(C.S.a (n+1))
    near (i:V) : separation (Lattice.wrap (C.side (n+1) p) (u i)) 0 ≤ t
    draw : 2*(a+2)*(C.S.a (n+1))< C.S.radius p
    fine : 2*(C.S.a m)*(1+((C.path.levels.budget m).B:ℝ)^2)<r
    sizeV : t ≤ 1024*((C.path.levels.budget (n+1)).B)^2
    lived (i:V): Cap (s i+2) (F i) 1
    cart : carton C (n+1) u F r
    occ : Fintype.card (Color V × Motion) ≤ C.path.levels.clock.J (n+1)
    scale : Warm C (n+1) (ℓ+1) k
    grade : d ≤ ℓ
    rank (i:V) : s i ≤ ℓ
local notation "U'"=> K
-- any tower produces Signature.Prices on ALL roots
variable {r a:ℝ} (H: Knock b n m p k d ℓ t r a C s u F)(x:(i:V)→Palette C (s i))(A:(i:V)→Sight C (s i) p)(U:(i:V)→Emblems C (s i))(P:Sight C d p)(S:Emblems C d)
local notation "s₁"=> (fun j:V=>Many.point (U j) (x j) m N)
variable (W:PulseC)(Y₀:J→Site (C.side b p))(T:J→Motion)(Z:∀ i:ℕ,ManyStem C Y₀ i→Body)
local notation "A!"=> Mine.tree Y₀ T
local notation "e!"=> (A!).labelY
local notation "ψ'"=> (A!).supportX
local notation "L"=> ManyStem C Y₀
local notation "λ'"=> T ∘ (A!).labelY ξ
variable (hO:GapAll ((C.path.levels.budget b).B^2+1+2*t) (C.side b p) Y₀)(hZ: ∀ i:ManyStem C Y₀ b, Cap (d+2) (Z b i) 1)(hz:PreparedA (Mine.tree Y₀ T) Z b (n+1) le_rfl)
variable (Q:ℝ)(hp:∀ i:V,size (x i)≤ Q)(hQ:0 < Q)
local notation "V'"=> Fintype.card (Color V)
local notation "u!"=> fee C m (n+1) ℓ k (Fintype.card (Color V)) Q
-- supply by vendor
include H Y hO hZ hz hQ hp
lemma granted : Records.Campaign (e! ξ) (ψ' ξ) λ' (o) s F (Z ξ) x k d ℓ m Q:=by
    let h' := H.level.trans n.le_succ; have hx:= cap_lives A! (fun _=>d) Z (le_refl b) h' le_rfl hz hZ
    refine ⟨fun i=> (lot (ψ' ξ) λ' u (shareO Y₀ T hO h') i).trans H.occ, inherited (ψ' ξ) _ u s F (Z ξ) (e! ξ) Y.tabs H.east.le H.cues H.near H.draw H.cart H.fine (fun i j hv=> grantG Y₀ Y.tabs hO h' _ _ hv), H.lived,hx,hp,hQ,H.scale,H.grade,H.rank,wreath (ψ' ξ) λ' u _ H.near H.sizeV⟩
-- all preimages. Signature.
variable (h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hW:Priced d W 1)(hU:Spine D B h b p d N P S)(hw:Awake D B b d)(hg:d+3 ≤ C.path.levels.clock.J n)(hN:m≤N)
local notation "he!"=> H.east.le.trans hN
local notation "X"=> bunchG (C:=C) (N:=N) (o) s F s₁
local notation "X'"=> dyes C (n+1) N p he! X
local notation "X'!"=> amplitude C n N p d W X'
local notation "e'"=> debit C n d (4*(1/u!))
include h hC hS h'A hN hw hW hU hg
lemma supplies (j:L n): ∃ R T, Signature C p b n N d h D P X'! e' R T:=by
    let l:=(A!).narrows n H.level; let ι(v:Address.Bud C p n):=l.symm (j,v)
    have he(i):ψ' ξ (ι i)= affine (T (e! n j)).1 ((K n p).ratio.embed (ψ' n j)) (Address.child C p n i)∧ λ' (ι i)= T (e! n j):=by
        have ht_ : (A!).narrows n H.level (ι i)=(j,i):= l.apply_symm_apply _
        rw [(A!).future n H.level, ht_]; simp only [Function.comp_apply,(A!).loyal n H.level,ht_]; exact ⟨rfl,trivial⟩
    exact starts_record h Y hC hS (e! ξ) (ψ' ξ) λ' o s F (Z ξ) Q x P S A U H.east hN h'A (granted Y s u F H x Y₀ T Z hO hZ hz Q hp hQ) W (T (e! n j)) (ψ' n j) ι hw hU H.level hg hW he
omit hW
variable (hPin:∀ i:ℕ,b ≤ i → Pin C i d) {e:ℝ} {R:ℕ→ Palette C d} {F₁:∀ i:ℕ,Tape G (C.side i p)}
local notation "M"=> finer S (show n ≤ m from Nat.le_trans n.le_succ H.east.le) (R n- Shadow.advances S R b n)
-- receipt campaign applies to SIGNED unit.V original.
local notation "Q!"=> Shadow.safe C d n e u! (4*(1/u!))
local notation "x!"=> Records.rebirth C d n p N he! W (Many.point S M m N) X
local notation "Z₁"=> swell he! A! (fun _=>d) (fun _=> x!) Z
include hW hPin
-- apply signs to full terminal mode.Budget
set_option maxHeartbeats 600000 in
lemma signals (hξ:Signature C p b n N d h D P X'! e R F₁)(hr:size (M) ≤ Q): 0< Q! ∧
    ‖C.omega N p (fun V=> ∏ i:L b, Z₁ b i V)‖*(focus C Q! n b)^(Fintype.card (L b)) ≤ Real.exp ((Fintype.card (Site (C.side b p)):ℝ)* Vac.treasury C.path.levels b+ Fintype.card (L b)*(2*Shadow.salary C b d+2)):=by
     obtain ⟨ht,hk⟩:= Records.signs h Y hC hS o s F x P S A U H.east hN W hw hU h'A hW H.level hξ A! Z (granted Y s u F H x Y₀ T Z hO hZ hz Q hp hQ) hr hZ hz hg hPin (fun i hi _=> shareB Y₀ T hO hi (hPin _ le_rfl)) (fun i hi _=> priceD Y₀ T Y.tabs hO hi)
     -- dec instance uniform.Note Fintype in L.Max
     let w:=(Mine.ward Y₀ T (Stock.census J) b); let g:=Mine.remap Y₀ T; let I:=(Finset.univ:Finset (ManyStem C Y₀ b)); let s:w.Mode:=⟨I,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨Finset.mem_univ _,g.injective.injOn⟩⟩⟩
     refine ⟨ht,?_⟩; have hx:= hk s; rw [show s.val.card=Fintype.card (L b) from Finset.card_univ] at hx; exact hx
end
end YM.RG05Readout.Halls
