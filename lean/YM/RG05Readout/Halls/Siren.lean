import YM.RG05Readout.Halls.Signal
/-!
# Common receipt at every boundary root, on the actual Family and units

Produce signatures from authenticated cluster. Compute M from that signature.
Payable on any census with Housed map; normalize partition and take ALL-copy
root before precision. Quotation on UNNORMALIZED engineer powers (not yet
restored to continuum R-integral coordinates). No root estimate claimed off
these tickets. Consumers for shifted chambers/internal probes must maintain
support margins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion Cells
open Overlay Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g ℓ t:ℕ}
set_option quotPrecheck false
local notation "Θ"=> C.path.levels
local notation "S'"=> C.S
local notation "Πξ"=> C.S.toDepth
local notation "K"=> C.path.levels.clock.op
local notation "λ₀"=> C.path.levels.clock
local notation "α"=> C.S.a
local notation "λ!"=> C.side
local notation "ω"=> Lattice.wrap
local notation "Z!"=>C.path.levels.budget
local notation "P!"=> C.side b p
local notation "ξ"=> n+1
local notation "V'"=> Fintype.card (Color V)
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D) (s:V→ℕ)(u: V→ Cover)(F:V→Body) {r a:ℝ}
    (H: Knock b n m p k d ℓ t r a C s u F)(x:(i:V)→Palette C (s i))(A:(i:V)→Sight C (s i) p)(U:(i:V)→Emblems C (s i))(P:Sight C d p)(S:Emblems C d)
    (W:PulseC)(hW: Priced d W 1)
local notation "o"=> (fun j:V=>Lattice.wrap (C.side (n+1) p) (u j))
local notation "s₁"=> (fun j:V=> Many.point (U j) (x j) m N)
variable (Q:ℝ)(hp:∀ i:V,size (x i)≤ Q)(hQ:0 < Q)
variable (h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hU:Spine D B h b p d N P S)(hw:Awake D B b d)(hg:d+3 ≤ C.path.levels.clock.J n)(hN:m≤N)
local notation "u!"=> fee C m (n+1) ℓ k (Fintype.card (Color V)) Q
local notation "he"=> H.east.le.trans hN
local notation "X"=>bunchG (C:=C) (N:=N) (o) s F s₁
local notation "X'"=>dyes C (n+1) N p he X
local notation "X'!"=>amplitude C n N p d W X'
local notation "eℓPn"=>debit C n d (4*(1/u!))
local notation "hb!"=> (H.level.trans n.le_succ).trans he
-- produce without boarding a single unattached root replica, no volume harm
include h h'A Y hC hS H hp hU hN hw hQ hg hW
lemma originates : ∃ R T, Signature C p b n N d h D P X'! eℓPn R T:=by
    let y:Unit→Site (C.side b p) := fun _=>0; let l:Unit → Motion:=fun _=>(1,false); let I' := ManyStem C y; let q: I' b →Body:= fun _=>0
    let T:= Mine.tree y l; let Z:= headings y l q; have hp' : ∃ j:I' n, True:=by
        let L':=(Πξ H.level p); exact ⟨⟨((),L'.embed 0), fun _=> L'.embed_parent _⟩,trivial⟩
    have hZ:= Many.headlines y l q (N:=ξ); have hp'': GapAll ((Z! b).B^2+1+2*t) (C.side b p) y:= fun _ _ heℓ=> (heℓ (Subsingleton.elim ..)).elim
    exact supplies h Y hC hS s u F H x A U P S W y l Z hp'' (fun i=> by unfold Z; rw [hZ.1]; exact (zero_basis _).increase zero_le_one) hZ.2 Q hp hQ h'A hW hU hw hg hN hp'.choose

-- universal Signature in orientation of H then tally.Signs
variable (hPin:∀ i:ℕ,b ≤ i → Pin C i d) {e:ℝ} {R:ℕ→ Palette C d} {T:∀ i:ℕ,Tape G (C.side i p)}
local notation "M"=> finer S (show n ≤ m from Nat.le_trans n.le_succ H.east.le) (R n- Shadow.advances S R b n)
local notation "Q!"=> Shadow.safe C d n e u! (4*(1/u!))
local notation "x!"=> Records.rebirth C d n p N he W (Many.point S M m N) X
local notation "L"=> Site (C.side j p)
noncomputable def baseT (C:Family G)(j b d:ℕ):ℝ:= (C.S.a j/C.S.a b)^4* Vac.treasury C.path.levels b+2*Shadow.salary C b d+2
include hPin
set_option maxHeartbeats 830000 in
-- this is dimensionless root norm suppressing exponent.Requires signed campaign cost
lemma realNorm (hξ:Signature C p b n N d h D P X'! e R T)(hr:size (M)≤ Q) (ht:j ≤ b)(A':Stock.Tabs.opens C.path.levels (bumper (2*t)) j b)
   (z:Site (C.side b p))(hf:separation z 0 ≤ (C.S.toDepth ht p).count.val/4)(q:Body)(hz:Cap (d+2) q 1):
    0< Q!∧ (Cells.center C.S p (ht.trans hb!) 0).rootTest (C.beta N p) (uniform C ξ p N d he x! b z (1,false) q) ≤ Real.exp (baseT C j b d)/ (focus C Q! n b):=by
    let x':=x!; let E':= uniform C ξ p N d he x' b z (1,false) q
    let L' := housed j ht z; let V!:= Site (C.side j p); let D' :=ManyStem C L'; let W':= hands C p j; let Q':= fun _ : D' b=> q; let Z:= Mine.tree L' W'; let P' := headings L' W' Q'
    have hB:=house_gap j ht z _ (opened_lot j ht _ A') hf
    obtain ⟨hb,hS₁⟩:= Many.headlines L' W' Q' (N:=ξ)
    have hz':∀ i: ManyStem C L' b, Cap (d+2) (P' b i) 1:=fun i=> by unfold P'; rw [hb]; exact hz
    obtain ⟨hw,hq⟩:= signals h Y hC hS s u F H x A U P S W L' W' P' hB hz' hS₁ Q hp hQ h'A hW hU hw hg hN hPin hξ hr -- shadow var hS wrong
    refine ⟨hw,?_⟩
    let QZ:= Cells.center C.S p (ht.trans hb!) 0; let v:=swell he Z (fun _=>d) (fun _=> x') P' b
    let eℓ:=Mine.remap L' W'
    have hu : C.omega N p (fun V₁=>∏ i:D' b,v i V₁) = moment (C.beta N p) (fun V₁=> ∏ i:L, QZ.copy i E' V₁):=by
       unfold Family.omega; congr 1; funext V₁; rw [← Equiv.prod_comp eℓ.symm]; refine Finset.prod_congr rfl (fun i _=>?_)
       have ht' :=ht.trans hb!
       let q':= (hands C p j i); let f₁:= (crops C ξ p N d he x' b (H.level.trans n.le_succ) q); let R':=(C.S.toDepth hb! p)
       have h_P: E' = stepUp (1,false) (R'.embed z) f₁:=dif_pos (H.level.trans n.le_succ)
       have hf:= (handmove C N p j ht' E' i); rw [elev C j p N ht' i,h_P,embed_comp (Πξ ht p) R',Records.stair_rot] at hf; rw [show v (eℓ.symm i)=stepUp q' (R'.embed (L' i)) f₁ from ?_]; exact congr_fun (h_P.symm ▸ hf) V₁
       unfold v swell uniform; rw [dif_pos (H.level.trans n.le_succ),show P' b=Q' from hb]; rfl
    change ‖C.omega N p (fun V₁=>∏ i:D' b,v i V₁)‖ * _^ (Fintype.card (ManyStem C L' b)) ≤ _ at hq; have hi:= Fintype.card_congr eℓ
    let M':=Fintype.card L; let a:=‖moment (C.beta N p) (fun V₁=> ∏ i:L,QZ.copy i E' V₁)‖
    rw [hu, hi,Stock.tallies C.S j b p] at hq; change a*_ ^ M' ≤ _ at hq
    refine Stock.spacer a (baseT C j b d) (focus C Q! n b) M' (norm_nonneg _) (focus_ge hw) Fintype.card_pos (le_trans hq ?_); apply le_of_eq (congr_arg _ ?_); unfold M' baseT; ring
end YM.RG05Readout.Halls
