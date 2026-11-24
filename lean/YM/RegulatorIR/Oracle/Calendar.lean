import YM.RegulatorIR.Oracle.Archive
import YM.Branch.Pick
import YM.Pert.Bulk.Keys

/-! Shape schedule genuine common linear context. `K.kernel` externally
chosen when applying to shared C. Reuse generous ALL-patch catalog. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping
open Next.Free (Catalog)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X:Type} {M:X→ℕ} {n:Page M→Side}
structure Program (K:KernelChoices) where
 receipt : MapPrices
 fees : ℕ→ℝ
 sectionD : ℕ→ ℝ
 startL : ℕ→ℕ
 hailed : Next.Free.Catalog K receipt fees sectionD startL

def books (K:KernelChoices): Program K:= Classical.choice (show Nonempty _ from by obtain ⟨v,p,q,s,h⟩:= Next.Free.pledges K; exact ⟨⟨v,p,q,s,h⟩⟩)

-- arbitrary $ℓ,P$ physical units. no actual RG witness assumed. $J$ values at neighboring levels. Uses one $Ratio`. Can be post prescribed by W1 window. Budget eligibility later.
structure Circuit {X:Type}(M:X→ℕ)(n:Page M→Side) where
 l : Page M→ℝ
 P : X→ℝ
 sizeL : Flap M → Side
 J : Page M→ℕ
 seats i: n i.prev=n i.next*sizeL i
 odd i: Odd (sizeL i).val
 holds i: 3 ≤ (sizeL i).val
 stands i: 4 ≤ (n i).val
 dual i: Even (n i).val
 week p: 4 ≤ J p
 shakes (i:Flap M): J i.next ≤ J i.prev
 slow (i:Flap M): J i.prev ≤ J i.next+1
 l_p i: 0< l i
 comet i: l i*(n i).val=P i.bindW

namespace Circuit
variable (S:Circuit M n)
include S
lemma width_s (i:Flap M): S.l i.next=S.l i.prev*(S.sizeL i).val := by
 refine mul_right_cancel₀ (b:=(↑(n i.next).val:ℝ)) (by positivity) ?_; rw [S.comet,mul_assoc,mul_comm (↑(S.sizeL i).val:ℝ),←Nat.cast_mul,← PNat.mul_coe,← S.seats,S.comet];rfl
lemma synchronize (w : X):0<S.P w:= by rw [← show _=S.P w from S.comet (Page.opening M w)];exact mul_pos (S.l_p _) (by positivity)
def pactP (i:Flap M): Patch:= ⟨S.sizeL i,S.J i.prev,S.week _,S.holds i,S.odd i⟩
def rail (K:KernelChoices)(i:Flap M): StepData (n i.next) (n i.prev):=⟨S.pactP i,K,congr_arg Subtype.val (S.seats i)⟩
-- Next.Free.Train direction

def acts (i:Flap M) (L:Next.Free.Train (S.J i.prev)) : Next.Free.Flight (S.J i.prev) (S.J i.next):= ⟨S.sizeL i,S.odd i,S.holds i,S.week i.prev,S.shakes i,S.slow i,L⟩
def training : ∀ i:Page M,Next.Free.Train (S.J i):= Halo.seriesC (X:=fun i=> Next.Free.Train (S.J i)) (fun _=> Next.Free.Train.top _) (fun i v=> (S.acts i v).land)

def crew (i:Flap M):= S.acts i (S.training i.prev)
lemma crest (i: Flap M): S.training i.next= (S.crew i).land:= Halo.laterC i
variable {K:KernelChoices}(Y:Program K)
-- top all n. coherence through f and p
private def wishes (x:ℝ)(h:0<x): Clip:= ⟨x,x/32,1,h,div_pos h (by norm_num),by linarith,zero_lt_one⟩

def clips (r:Page M): Clip:= wishes (Y.sectionD (S.J r)) (Y.hailed.fit (S.J r))
structure Certificate (r:Page M) (B:Bed):Prop where
 card : let j:=S.J r; Hall B (Y.receipt.α j) (Y.receipt.Ω j) (Y.receipt.η j) (S.clips Y r)
 flight_s : Next.Free.Defined K.penalty (Y.fees (S.J r)) (S.training r) B
 symmetryP :∀ n G,Bid.Sworn B n G
 top_s : S.training r= Next.Free.Train.top _→∀ p:Side,B.diagonal.acts p=1
include Y
lemma dreams r: ∃ B, Certificate S Y r B:=by
 obtain ⟨B,h,hp,he,ht,hV⟩:= Y.hailed.bottom _ (S.week r) (S.clips Y r) (le_refl _) (S.training r)
 exact ⟨B,⟨⟨hp,he,Pert.Bulk.merit hp,Y.receipt.alpha_pos _,Y.receipt.eta_pos _⟩,h,ht,hV⟩⟩

def tables (r):= (dreams S Y r).choose
lemma honored (r):Certificate S Y r (S.tables Y r):=(dreams S Y r).choose_spec

def tells (_ : Program K)(w:Flap M): Cross (S.sizeL w) (TypeFace 1) (TypeFace 1):= ((S.crew w).duo K.penalty).A0
lemma predicted (i:Flap M) : let r:= S.J i.prev;
                               BidP (S.pactP i) K (S.tables Y i.prev) (S.tables Y i.next) (S.tells Y i) (Y.receipt.α r) (lesser (Y.receipt.Ω r) (S.sizeL i)):=by
 intro r;let a:=Y.receipt;let L:=S.pactP i;let W:=S.crew i
 let s:= S.J i.next; have hm:Next.Free.Mag r s:= ⟨S.week _,S.week _,by have he:s≤ r:= S.shakes _;have h:r≤ s+1:= S.slow _;omega⟩
 have hz:Next.Free.HopQuote K r s _ _ _ _ _ _ := Y.hailed.hop r s hm
 have hp:= S.honored Y i.prev; have hx:= S.honored Y i.next
 constructor
 · have he:= ((hz W).1 [] (by simp)).1
   change Row.strip _ _ _; exact (by simpa only [List.length_nil,Nat.add_zero,Nat.zero_add,pow_one] using! he)
 · exact div_nonneg (hp.card.paid) (by positivity:0 ≤ ((S.sizeL i).val:ℝ))
 intro n
 have he:=Next.Free.diagonal (c:=n) (f:=n*L.L) K (Y.fees s) (Y.fees r) (Y.hailed.net _) (Y.hailed.net _) W (S.week _) _ (S.tables Y i.next) hp.flight_s (by rw [show W.land=_ from Eq.symm (S.crest i)]; exact hx.flight_s) rfl
 exact he.trial

end Circuit
end YM.RegulatorIR.Oracle
