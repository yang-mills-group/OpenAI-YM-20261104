import YM.Contact.Palm
import YM.MergeProof.North.Brim
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d w:ℕ)(h:ℤ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (x:Cover)(B: C.label d) (T:C.label w) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (hj:j<N)
abbrev radiusJ:= fuga C.path.levels (m+1)
def chip (B:C.label d)(T:C.label w)(x:Cover)(v:C.label D) (U: Config G (C.side N p)) : ℂ:= ((radiusJ C m:ℂ)^h * C.seen ⟨w,T⟩ (Cells.location C.S j N p x) U)*C.seen ⟨d,B⟩ (0: Site (C.side N p)) U-C.seen ⟨D,v⟩ 0 U
local notation "f"=> chip C N p j m D d w h B T x
local notation "τ"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hj.le)))) 0
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
def twoStakes (i:Bool):=if i then plumR C w b j/(rad)^h else plumR C d a j
local notation "A"=> twoStakes C j m d w h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level w).coeffSize T ≤ b)
local notation "ℓ"=> wrap (C.side j p) x
local notation "L"=> bites C J j p ℓ
local notation "O"=> Cells.location C.S j N p x
local notation "W'"=> holder C.path.levels j m δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "k₀"=> scurry C.path.levels r χ η (m+1)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hj.le)
local notation "B!"=> ((P').B^2+1+2*blast C.path.levels m)
variable (scale:ℝ) (hρ:fuga C.path.levels (m+1) ≤ scale) (hρ':scale ≤ ranula C.path.levels m)
include hh hp hR hB hT hρ hρ'
set_option maxHeartbeats 800000 in
lemma wallSupply (ha:0<a)(hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref w ≤ j)(hW:scale/16≤ ‖C.S.place ℓ‖)(hw':‖C.S.place ℓ‖ ≤4*scale)(he:Interior ((τ).chamber 0) (C.O N p T O))(hs:Interior ((τ).chamber 0) (C.O N p B 0))(he':∀ z:C.label D, Interior ((τ).chamber 0) (C.O N p z 0))
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ Y' H')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ: B! ≤ (C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   ∃ z:C.label D,Next.UVStress.quota C D m N p z ≤ 2*e∧ Interior ((τ).chamber 0) (f z) ∧ (τ).rootTest (C.beta N p) (f z) ≤ 2*(stakes C J k / c):=by
   obtain ⟨σ,hZ⟩:=hr.city; let R':ℂ:= (↑(rad):ℂ)^h; let M:= C.O N p B 0; let U:=R' • C.O N p T O
   have hA' z: (f z)=M*U-C.O N p z 0:=by funext i; change R'*(C.O N p T (O) i)*M i-C.O N p (d:=D) z 0 i = M i*(R' *_)- _; ring
   have hΔ := hI.trans m.le_succ; let t:Bool→ℕ:= Bool.rec d w; let t':Π i:Bool,C.label (t i):= Bool.rec (motive:=fun i=> C.label (t i)) B (R' • T)
   let s:Bool→ Config G (C.side N p)→ℂ:= Bool.rec M U
   have hX (i:Bool): s i= C.O N p (t' i) (L N (0,i)):= by
      cases i
      · rw [biteF,zeroMama C J p N (by omega)]
      rw [biteT C J j p N ℓ (by omega), vect C j p N ℓ hj.le, show (C.S.toDepth hj.le p).embed ℓ= O from by rw [Cells.location,dif_pos hj.le]]
      exact ((C.linearO N p w O).mk' _ |>.map_smul R' T).symm
   have hμ(i:Bool): Interior ((τ).chamber 0) (s i):=by cases i; exact hs; exact he.scale _
   have hv(i:Bool): A i * Spindle.paid C (t i) j N p (t' i) ≤ fly C.path.levels (t i) j :=by
      cases i
      · exact paid_new C N p j d hh B a ha hB h' hj
      change plumR C w b j/(rad)^h * Spindle.paid C w j N p (R' • T) ≤ _; rw [paid_scale C N p j w hh hp hT' T R' hj.le,show ‖R'‖=(rad)^h from by unfold R';rw [norm_zpow,Complex.norm_real, Real.norm_of_nonneg (fugap C m|>.le)],←mul_assoc,div_mul_cancel₀ _ (zpow_pos (fugap _ _) _|>.ne')]; exact paid_new C N p j w hh T b hb hT hT' hj
   have hyP(i:Bool):0<A i:=by
      dsimp only [twoStakes]; split
      · exact div_pos (stockpit _ _ _ _ hb) (zpow_pos (fugap _ _) _)
      exact stockpit _ _ _ _ ha
   subst X η; obtain ⟨z,hz,hU⟩:= shipment C N m p D J k c A ℓ hf hk hj hm t t' hh hp hI hR scale r₀ hx hK (Bool.rec (motive:=fun i=> C.ref (t i) ≤ j) h' hT') hv hyP hR' hΩ hW hw' s (fun i=>by rw [hX i]; exact (itemT C N p _ hh (t' i) (L N (0,i))).symm) (fun i=> by rw [hX i]; exact C.continuousO ..) hμ he' hZ (hr.funs _ hΔ|>.1) (hr.funs _ hΔ|>.2) (hr.brings m hI N p _|>.2) (hr.dollars m hI) (hr.crisp j (by omega)) (fun i he hi=>hr.brings i (by omega) N p (hi.trans hj)|>.1) (hr.bars _ hΔ|>.1) (hr.bars _ hΔ|>.2) hw hL hρ hρ' hV hA hC
   refine ⟨z,hz,?_⟩; rw [hA' z] -- target exists not yet
   exact ⟨Next.UVStress.minus ((hμ false).times (hμ true)) (he' _),hU⟩
end
end YM.MergeProof.Ribbons
