import YM.OPE.Laying.Sleight
import YM.OPE.Log.Fees
/-! # Ledger produced with a clock and clamps -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
open Mask Extra.Histories.Relay Next.Rank Studio
noncomputable def earn (C:Family G)(φ:I→ℕ)(v:I→ ℝ)(m:ℕ)(i:I) := stair (near C.path.levels) (v i) (φ i) m
lemma earning_here (v:I→ℝ)(i:I) (hp:0<v i): earn C φ v (φ i) i=v i :=by unfold earn stair; rw [marines (φ i) η₀ _ (fun _=>hp)]
lemma earning_prev {a:ℕ→ℝ}{x:ℝ}{m k:ℕ}(h:k ≤ m): stair a x m k=x:=by
    induction k with
    | zero=>rfl
    | succ i IH=> unfold stair; rw [march,if_neg (by omega)]
-- easier use η>0 & ≤1 purchases. 
include L
lemma earns (he:∀ i,0<W₀ 0 i) : Lenient η₀ φ (earn C φ (W₀ 0)):=by -- replace by v, no synthetic type
    have hΘ(k):= L.system.costs.stay.water k (Nat.zero_le k)|>.1
    have hη(k): η₀ k ≤ 1:= inv_le_one_of_one_le₀ ((Y).fits.delayed (k+1)|>.le)
    have ht(k:I) m (he:φ k ≤ m): earn C φ (W₀ 0) (m+1) k= η₀ m*earn C φ (W₀ 0) m k:=by unfold earn stair; rw [march,if_pos he]
    refine ⟨fun i k=>?_,fun k i hi=>?_,fun k i=>?_⟩
    · by_cases h:k ≤ φ i
      · unfold earn; rw [earning_prev h]; exact he i
      exact march_pos C.path (φ i) (renal C.path.levels) η₀ _ (fun _=>he i) ⟨fun k _=> L.system.costs.stay.water k (Nat.zero_le _),fun k _=>L.system.costs.stay.mint k (Nat.zero_le _),fun k _=>L.system.costs.stay.split k (Nat.zero_le _),fun k _=> L.system.costs.stay.support k (Nat.zero_le _)⟩ k (by omega) ()
    · exact (earning_prev hi).trans (earning_here _ k (he k)).symm
    by_cases h:φ k ≤ i
    · rw [ht _ _ h]
    rw [show earn C φ (W₀ 0) i k=W₀ 0 k from earning_prev (by omega), show earn C φ (W₀ 0) (i+1) k=W₀ 0 k from earning_prev (by omega)]; exact mul_le_of_le_one_left (he k|>.le) (hη i)

lemma birthCounter (i:ℕ){j:(C.labels.level d).Index}{g:Extra.Histories.Music (C.labels.level d) C.path N p}(hE:Studio.Series C W (waybill (Y)) D N p d g)(hk:C.ref d ≤ i)(he:i ≤ N): Next.UVStress.quota C d i N p ((C.factory d N p).terminal (az g i j))=1:=by rw [hE.quota _ hk he,LinearEquiv.symm_apply_apply,az,LinearEquiv.apply_symm_apply]; exact Size.size_axis _ j
-- buy on registry
noncomputable def birthClock (C:Family G)(i d:ℕ)(x:ℝ):ℝ:= fly C.path.levels d i / x * C.S.a i^d
omit L
lemma clock_pos (h:0<x):0<birthClock C i d x:= mul_pos (div_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans ((Y).fits.delayed _)) _)) h) (pow_pos (C.S.a_pos _) _)
include h L
lemma enters (d:I→ℕ)(A:I→ℝ)(v:(k:I)→ C.label (d k))(g:∀ k:I,Extra.Histories.Music (C.labels.level (d k)) C.path N p)(hp: b ≤ N)(hc:∀ k:I,b ≤ φ k ∧ φ k ≤ N)
    (hP:∀ k:I,Studio.Series C W (waybill C.path.levels) D N p (d k) (g k))(hS:Trial s) (hr:∀ i:ℕ,b ≤ i→i<N→∀ k,u i k=(Y|>.clock.op i p).ratio.parent (u (i+1) k))(h_V:Θ.occupied (r N) (u N))
    (hR:∀ k:I,C.ref (d k) ≤ φ k) (he: ∀ k,0<A k)(hk:∀ k:I,Next.UVStress.quota C (d k) (φ k) N p (v k) ≤ A k)
    (hT:∀ k:I,∀ m:ℕ,φ k ≤ m→ m<N → u (m+1) k=(Y|>.clock.op m p).ratio.embed (u m k)) : let rE:= earn C φ (fun k=>birthClock C (φ k) (d k) (A k));∃ P,Ledger Θ N s (fun k=>C.O N p (d:=d k) (v k) (u N k)) P u φ rE 1 D ∧∀ k,Mantle C.path N p (φ k) (C.localSection (d k)) (1,false) (u (φ k) k) (((g k).tone (φ k)).plays ((C.factory (d k) N p).terminal.symm (v k))) (P (φ k) k):=by
    intro w
    let y k:= birthClock C (φ k) (d k) (A k); let X(k):= C.O N p (d:=d k) (v k) (u N k)
    have h_W : Lenient η₀ φ w:= earns (W₀:=fun _=>y) L (fun i=> clock_pos (he i))
    have ht(k): y k*Spindle.paid C (d k) (φ k) N p (v k)≤ ζ (d k) (φ k):=by
       let a:= A k; have ha:= he k; unfold y birthClock; rw [mul_assoc,obey_quota]; exact (mul_le_mul_of_nonneg_left (hk k) (div_pos (L.system.grows _ _ (hR k)) ha|>.le)).trans_eq (div_mul_cancel₀ _ ha.ne')
    choose F' hE hξ hη using fun k=> (hP k).launch h L.system (v k) (fun i=>u i k) (hR k) (hc k|>.2) (clock_pos (he k)) (ht k) (hT k)
    let Y'(i k):=F' k i; have hΩ:lifted w 1=w:=funext (fun i=> funext fun k=>one_mul (w i k));
    refine ⟨Y',⟨hp,le_rfl,hS,hr,fun k=> C.continuousO .., hc,⟨one_pos,le_rfl⟩,h_W,?_,fun k=>?_⟩, fun k=>hη k (φ k) le_rfl (hc k|>.2)⟩
    · rw [hΩ]; exact Θ.generation s h.wilson L.system.costs.night hp h_V (fun k=>h_W.ready ..) hξ
    rw [hΩ]; exact hE k
end YM.OPE.Log.Book
