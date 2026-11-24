import YM.RemainderComparison.Fallow.Arrow
/-!
# Logical singleton projection on the marker-conditioned expression

Keeper runs after Passion.Both. tilts. Literal `Source.Coefficient` in the actual header and kernel conventions. Keeps `ζ` operator tests normalized before bases, connects X to Pet.R and bound. Before conversion on different bases by RG04, use representation supplying THESE commitments. No assumption chosen χ in Region matches a final stable graph.Via β conversion eventual.Se.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable [Fintype θ][DecidableEq θ](J:Census θ)
variable {i:θ}{D:ι→Finset θ}{z:ι→ Poly J}(X: Hol G) (F:Plane G n θ) (a:Audited Q)
local notation "L"=>F.visor i
set_option quotPrecheck false
local notation "F₀"=>(L).basis
local notation "τ"=> (L).sectionQ
local notation "o'"=>(L).origin
local notation "A" => Roll T R Z D
local notation "A₁"=> cash T p R Z F X SeatD.MaskType.exactM z D

def motto (J:Census θ) (z:ι→Poly J)(i:θ) (p:Multiset ι):ℂ:= (controls Z z p).part (J.fire i)

abbrev players (D:ι→Finset θ)(i:θ):= {b:Roll T R Z D // Passion.Ra T R Z F b=some i}
local notation "R₀" => players T R Z F D i

def salary (z:ι→ Poly J) (i:θ) (b:players T R Z F D i):ℂ:= motto Z J z i (T.marks b.val.val.val)
local notation "Wq" => salary T R Z J F z i

def crowns (z:ι→Poly J)(i:θ) (b: players T R Z F D i) : (F.visor i).basis.Coeff:= (salary T R Z J F z i b) • (PairAt T p R Z F X b.val a i).header


def kernels (z:ι→Poly J) (i:θ)(b:players T R Z F D i): Config G n→ℂ:= (salary T R Z J F z i b) • (Complex.ofReal ∘ (PairAt T p R Z F X b.val a i).entry)
local notation "δp" => crowns T p R Z J X F a z i -- binder X order?
local notation "Rφ" => kernels T p R Z J X F a z i
variable (hp:Passion.Oriented D J Z z)(he:F.exam i)
include he hp
omit [Fintype θ] in
lemma extraP (b:A)(hv: Ra T R Z F b ≠ some i) (U:Config G n): ((A₁ a U b).part (J.fire i))=0:=by
    unfold cash; rw [Poly.part_smul]; apply mul_eq_zero_of_right; by_contra hn; have hh:=pedigree hp i hn; exact hv ((Passion.charted T R Z F b i).mpr ⟨hh,he⟩)
omit hp he
variable {σ b t e w:ℝ}{l k:ℕ}
variable (h:Precepts T p R Z D σ b)(hr:AxisG p F X t l e)
include h hr
variable (U:Config G n)
omit [Fintype θ] in
lemma voices (hp:players T R Z F D i) : ((cash T p R Z F X SeatD.MaskType.exactM z D a U hp.val).part (J.fire i))= Local.primary τ o' p.threshold (δp hp) U+
    masked p.threshold (area T R Z F hp.val) (Rφ hp) U:=by
    let q:= PairAt T p R Z F X hp.val a i
    let K:= T.halls hp.val.val.val -- .val.ap
    have hg := ((charted T R Z F _ i).1 hp.prop).2
    have he := SeatD.plucked p L X K q U (hr.growth i hg) ((Passion.opal T p R Z F X .exactM hp.val a i h hp.prop hr).header)
    have hh : area T R Z F hp.val= Local.joint τ o' K:=by unfold area; rw [hp.prop]
    rw [show ((A₁ a U hp.val).part (J.fire i))= Complex.ofReal (amount T p R Z F X SeatD.MaskType.exactM hp.val a U) *(salary T R Z J F z i hp) from by unfold cash; rw [Poly.part_smul]; rfl,hh]
    have hx : ∀ (x:Config G n) (f:ℂ) (g:Config G n→ℂ), RG.masked p.threshold (Local.joint τ o' K) (f • g) x= f • (RG.masked p.threshold (Local.joint τ o' K) g x):=by intro x f g; exact congr_fun (Local.maskLinear _ _ |>.map_smul f g) x
    unfold Passion.amount; rw [hp.prop]; change (↑(SeatD.sharp p L K .exactM q U):ℂ) *_=_; rw [show Rφ hp= Wq hp • (⇑Complex.ofRealCLM ∘ q.entry) from rfl,he,hx U (Wq hp) (Complex.ofRealCLM ∘ q.entry)] -- expand kernels & ofReal vs CLM
    unfold crowns; rw [map_smul,Pi.smul_apply]; change (Local.primary τ o' p.threshold q.header U+ _)*_ = Wq hp • (Local.primary τ o' p.threshold q.header U) + _; rw [add_mul]; exact congr_arg₂ (· +·) (mul_comm ..) (mul_comm ..)
end YM.RemainderComparison.Fallow
