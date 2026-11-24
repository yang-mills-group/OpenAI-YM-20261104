import YM.QuadraticLocal.Class.Spill
import YM.QuadraticLocal.Tint.Patrol

/-! # Startup re-expression of entire off-mask analytic polynomials (incl. global)

For installation at a cutoff or initial level. Countable charts and roots retained. The
field-dependent conditional formal denominator is upstream of this calculation (because `X`
can already be in log prescription). No assumption that a Shelf source mark is unforced
outside off-mask pieces: *this* constructs the partners even there. For other realizations
(e.g. smaller forced tails that are data of the field), the input side must also keep the actual
stipulated partners and tests. The repeated output step uses **any** `Pupil` satisfying the caps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spill.Foundry

open Function Filter Finset Wilson Lattice RG Marker Ac Push Push.AbsoluteSums MeasureTheory
open Corrected Earn Canopy Kiosk Next.Scheduling
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge} {n:Side} {α:Type}
variable {V ι:Type}[DecidableEq V]{R:Census V}{D:Passport n V}
variable (P:Rep G n) -- current
variable (X: ι→ Row D R G α) (g:ℝ) (s:ℕ) (i:ι)
variable {w:V→ℝ}{a b f τ c k z η:ℝ} [Countable ι]

set_option quotPrecheck false
local notation "B"=> P.p
local notation "Λ"=> Spill.shifts X B g
open Affinity Fusion Fusion.Attached
variable {F:Activities G n}(W: Second P.p F P.activities a f P.p.supportExponent b )(hf:Hard.Rent F.forced F.K P.p (P.p.supportExponent+1) a)

def noneL (o:V→Site n) : Lamps α Empty G P.p o R:= ⟨(fun i=>i.elim), (fun i=>i.elim), (fun i=>i.elim), (fun i=>i.elim), fun _ u=> u.elim, fun _ u=> u.elim, (fun i=>i.elim),fun _ u=> u.elim⟩
local notation "T"=> (noneL (α:=α) (R:=R) P D.origin)

def intake : Tint.Incoming D P α Empty R:= ⟨T, Kiosk.Second.canopy (Hard.rent hf) Λ W⟩
local notation "Μ"=> intake P X g W hf

variable {Y:V→Type}[∀ i,AddCommGroup (Y i)][∀ i,Module ℝ (Y i)]
variable {Actors:∀ i,Set (Y i)}{K:∀ i,Submodule ℝ (Y i)}
variable {U:ι→ Row D R G (Affinity.Wallet Actors)}
local notation "Μ'"=> (intake P U g W hf)
lemma retention (hU:Tableau K Actors U): Affinity.Taut D.support Actors K (Μ').old ∧ Affinity.Crown D.support Actors K (Μ').hard:= by
 refine ⟨⟨(fun i=> i.elim),(fun i=> i.elim)⟩, Affinity.Crown.second _ W ( Spill.shifts U B g ) ?_ (fun i q=> Spill.retains B g i hU q)⟩
 refine ⟨fun i u=> Affinity.Stencil.const (Poly.bead R (↑(F.K i u):ℂ)) fun i hi=>?_⟩
 exact (Poly.part_send ..).trans (if_neg hi)

lemma empty_lit (Z:Tint.Incoming D P α Empty R) (j:ℝ)(v:ℕ): Z.old.Paid w v j 0:=
 ⟨ Empty.elim,(fun i=> i.elim),(fun i=> i.elim), fun x=> budget_finite (fun i=> i.elim) (by rw [Finset.univ_eq_empty,Finset.sum_empty])⟩
local notation "z'"=> P.p.supportExponent+1
variable {Β h q:ℕ} {θ μ d J:ℝ} {t:V→ℕ}
variable (hC:Scene.Armada X w t μ c q h Β)(hJ: Invoice.Supports P.p z (P.p.supportExponent+1) g μ θ)
local notation "w₀"=> Stoop.radius w d
local notation "r"=> q+Β+1
local notation "I_"=> Invoice.price B z (q+Β+1) h (P.p.supportExponent+1) θ G
variable (ht:1≤ d)(hℓ : Spill.allOver P.p ^ (q+Β+1) * ( Invoice.price P.p z (q+Β+1) h (P.p.supportExponent+1) θ G * c ) ≤ b*d )
local notation "F_"=> F
include hC hJ ht hℓ
omit [Countable ι] in
private lemma loan : (Λ).Budget w₀ P.p.B (P.p.supportExponent+1) b:=by
 have H:= Spill.allowance X B g hC hJ ht
 obtain ⟨f,hM,hH⟩:= H.earned
 have hv : 0<d:= zero_lt_one.trans_le ht
 refine ⟨f,hM,fun i=> budget_loosen (hH i) ?_⟩
 apply le_trans (le_of_eq ((?_): _=(Spill.allOver P.p ^ (q+Β+1) * ( (I_) * c ))/d )) ((div_le_iff₀ hv).mpr hℓ)
 ring
variable [Fintype V]
lemma prices : (Μ).hard.Paid w P.p.B P.p.supportExponent (d^h*f):= by
 have hx:= (hC.stored ht).positive
 exact Stoop.budget _ hC.quota _ hC.positive ht (Hard.Rent.instals hx W hf Λ P.p.exponent_pos.le (loan P X g hC hJ ht hℓ)).1

local notation "Σ_"=> (Tint.Patrol.picture X (Μ) )
local notation "μ_"=> rendered X P.p g

omit hC hJ ht hℓ in
def uncut (t':α) (U:Config G n): Poly R:= ∑' i, Spill.raw X g t' i U
local notation "Y_"=> Foundry.uncut X g
open GridRenewal.Rain
variable (hg:g=ConnectedActivityE6.Coat.gStep P.beta)
include hg
lemma value (y:α)(Q:Config G n):
     Summable (fun i=> Spill.raw X g y i Q) ∧
     (Σ_).E.log y Q=(μ_).log y Q ∧
     (Σ_).density y Q=((↑(P.eval Q):ℂ)) • Poly.pass (Y_ y Q):=by
 have hz : (Σ_).E=(μ_).join (Μ).old:=by
     dsimp only [Tint.Patrol.picture]; cases hg; rfl
 have he:= loan P X g hC hJ ht hℓ
 have hp:= (hC.stored ht).positive; let B':= Hard.Rent.instals hp W hf Λ P.p.exponent_pos.le he
 let A':= (μ_).log y Q; let Bx:= (Λ).log y Q
 have hr₀:0 ≤ P.p.supportExponent+1:= add_nonneg (P.p.exponent_pos.le) zero_le_one
 have hZ:= (Λ).earnings he hp hr₀ y Q
 have hW:= (Scene.Armada.paid _ _ _ hC P.p hJ).sums hr₀ hC.positive y Q
 have hX: HasSum (fun i=> Spill.raw X g y i Q) (A'+Bx):= (hW.hasSum.add hZ.hasSum).congr_fun (fun i=> Spill.raw_eq X P.p g y i Q)
 have ho: (Σ_).E.log y Q=A':= by
    rw [hz, Lamps.joinLog y Q hW, show (Μ).old.log y Q=0 from tsum_empty, add_zero]; exact (empty_lit P (Μ) z' P.p.B).sums hr₀ hC.positive y Q
 have hT: A'.part R.quiet=0:= Lamps.quiet_of_hasSum y Q hW
 have hY: Bx.part R.quiet=0:= by unfold Bx Canopy.ShiftRows.log; rw [Poly.share hZ]; simp_rw [(Λ).skip]; exact tsum_zero
 refine ⟨hX.summable,ho,?_⟩
 have he' : (Σ_).gas y Q=(↑(P.activities.gas P.p Q):ℂ) • Poly.pass Bx:= ( B'.2 y Q ).tsum_eq
 rw [ Gallery.density,ho,he', show Y_ y Q=A'+Bx from hX.tsum_eq, ← GridRenewal.Rain.passes (A'+Bx) (show _=0 from (by simp only [Poly.part_plus,hT,hY,add_zero])), GridRenewal.Rain.plus,GridRenewal.Rain.passes _ hT,GridRenewal.Rain.passes _ hY,Rep.eval,Complex.ofReal_mul,mul_smul_comm, smul_smul]

end YM.QuadraticLocal.Spill.Foundry
