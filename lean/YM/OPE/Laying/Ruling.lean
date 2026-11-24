import YM.OPE.Laying.Estate
/-!
# Carrying a menu of present and future marked insertions

Widths are not bounded below between the ranges where they're actually used.
Charge only exactly when a purchase or grouping done at the declared age.
Keeps actual Programs available at all times until then. Shaving is allocated
in units of a common positive number: AFTER any number of fine history
choices this can be regenerated. Or can sharpen by a polynomial-log factor at
each gathering (even if no collision interrupts the segment). Never pay
per-step shrink on long separated legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d :ℕ}{w x y :ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "B"=> Site (C.side b p)
local notation "E"=> standC C b N p
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V} {s:Ward (Names V I)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)}
structure Lenient (η:ℕ→ℝ) (φ:I→ℕ)(W:ℕ→I→ℝ) : Prop where
    ready i : ∀ m,0<W m i
    early i m: m ≤ φ i→ W m i=W (φ i) i
    paid i : ∀ m:ℕ, η m*W m i ≤ W (m+1) i

def lifted (W:ℕ→I→ℝ) (x:ℝ) (m:ℕ)(i:I):= x*W m i
lemma Lenient.scaleRight (h: Lenient η₀ φ W₀)(hp:0<x) : Lenient η₀ φ (lifted W₀ x):= ⟨fun i m=>mul_pos hp (h.ready i m), fun i m hz=> congr_arg (x*·) (h.early i m hz), fun i m=> by unfold lifted; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (h.paid i m) hp.le⟩
structure Ledger (Θ : Playout C.path p b N V)(j :ℕ) (s : Ward (Names V I))(F:I→ Config G (C.side N p)→ℂ) (P:∀ i:ℕ,I→ Cup (C.path.rep N p i))(u:∀ i:ℕ,I→ Site (C.side i p))(φ:I→ℕ)(W₀:ℕ→I→ℝ)(x:ℝ)(D:∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) : Prop where
    time : b ≤ j
    limit:j ≤ N
    trial : Trial s
    slots (k:ℕ) : b ≤ k→k < j → ∀ a,u k a=(C.path.levels.clock.op k p).ratio.parent (u (k+1) a)
    terms i:Continuous (F i)
    stock i : b ≤ φ i∧ φ i ≤ j
    rate : 0 < x∧ x ≤ 1
    clock : Lenient (near C.path.levels) φ W₀
    market : Θ.Market s (u j) (P j) (Θ.intention F j limit) (lifted W₀ x j) (ν j)
    progress i : Program C.path N p (φ i) j (fun m=>u m i) (fun m=>P m i) (fun m=>lifted W₀ x m i) D limit
variable (S:Ledger Θ j s F P u φ W₀ x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))
include S
namespace Ledger
lemma thinner (hi:0<y)(hx:y≤ x) : Ledger Θ j s F P u φ W₀ y D:=by
    refine ⟨S.time,S.limit,S.trial,S.slots,S.terms,S.stock,⟨hi,hx.trans S.rate.2⟩,S.clock, S.market.shy Θ ?_ ?_ le_rfl,fun i=>(S.progress i).within le_rfl le_rfl (fun j _ _=> ?_) (fun j _ _=> ?_) ⟩
    · exact fun i=> mul_pos hi (S.clock.ready ..)
    · exact fun i=> mul_le_mul_of_nonneg_right hx ((S.clock.ready ..).le)
    · exact (mul_pos hi (S.clock.ready ..)).le
    exact mul_le_mul_of_nonneg_right hx ((S.clock.ready ..).le)
include S L h
lemma steers (hK:C.ref 0 ≤ b) (hp:b ≤ k)(hh: k ≤ j)(hT:∀ i,φ i ≤ k)
    (hy:∀ m:ℕ,k ≤ m→m < j → Θ.occupied (r m) (u m) ∧ Θ.occupied (r m) (u (m+1)) ∧ Spaced s (Θ.spectrum m (u m)) ((C.path.levels.budget m).B * meter L m)) : Ledger Θ k s F P u φ W₀ x D:=by
    have he:= S.clock.scaleRight S.rate.1
    have ht := intervalMarket (L.guide h hK) S.trial hh hp hp S.limit (fun _ _ _ i=> he.ready ..) (fun i he' hv j'=>⟨S.slots i (hp.trans he') hv j',he.paid j' i⟩) hy S.market S.terms (fun i=> (S.progress i).within (hT i) le_rfl (fun j _ _=> (he.ready ..).le) (fun _ _ _=>le_rfl)) k le_rfl hh
    refine ⟨hp,hh.trans S.limit,S.trial,fun k' h=>(fun hk=>S.slots k' h (hk.trans_le hh)),S.terms,fun i=>⟨(S.stock i).1,hT i⟩,S.rate,S.clock,ht,fun i=>(S.progress i).within le_rfl hh (fun _ _ _=>(he.ready ..).le) (fun _ _ _=>le_rfl)⟩
end Ledger
end YM.OPE.Log.Book
