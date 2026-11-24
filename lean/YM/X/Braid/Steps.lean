import YM.X.Braid.Onion
/-!
# Weighted virgin (site-frame cut, shifted and unshifted). discrete finite sums with real-to-complex change convention.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric
open Reed Interval Hinge CellsInt
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {V:Type*}[AddCommGroup V][Module ℝ V]
abbrev Lane:= Cover →₀ ℝ
def beadR (χ: Lane)(f:Cover→V): V:= Finsupp.linearCombination ℝ f χ
def nudged (χ:Lane)(t:Cover): Lane:= χ.equivMapDomain (Equiv.addRight t) -- name
lemma nudge (χ:Lane)(t z:Cover): nudged χ t z=χ (z-t):= by rw [nudged,Finsupp.equivMapDomain_apply]; congr 1
lemma sendB (χ:Lane)(t:Cover)(f:Cover→V): beadR (nudged χ t) f= beadR χ (fun z=> f (z+t)):= by rw [beadR,nudged,Finsupp.equivMapDomain_eq_mapDomain,Finsupp.linearCombination_mapDomain];rfl
lemma beadLm {W:Type*}[AddCommGroup W][Module ℝ W](χ:Lane)(L:V→ₗ[ℝ] W)(f:Cover→V): L (beadR χ f)=beadR χ (L ∘ f):= LinearMap.map_finsupp_linearCombination .. -- supply
lemma bead_add (χ:Lane)(f g:Cover→V): beadR χ (f+g)=beadR χ f + beadR χ g:= by unfold beadR; simp [Finsupp.linearCombination_apply,Finsupp.sum, Finset.sum_add_distrib,smul_add]
lemma bead_sub (χ:Lane)(f g:Cover→V): beadR χ (f-g)=beadR χ f-beadR χ g:= by unfold beadR; simp [Finsupp.linearCombination_apply,Finsupp.sum, Finset.sum_sub_distrib,smul_sub]
lemma bead_neg (χ:Lane)(f:Cover→V):beadR χ (-f)= -beadR χ f:= by unfold beadR; simp [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_neg_distrib]
lemma bead_sum {I:Type*}(χ:Lane)(s:Finset I)(f:I→Cover→V): beadR χ (fun z=>∑ i∈s,f i z)=∑ i∈s,beadR χ (f i):= by unfold beadR; simp_rw [Finsupp.linearCombination_apply, Finsupp.sum,Finset.smul_sum]; rw [Finset.sum_comm]
lemma plaq_turn (f: Axis→Axis→V)(h:∀ i,f i i=0) : ∑ i:PlaqAxes,(f i.val.1 i.val.2+f i.val.2 i.val.1)=∑ i:Axis, ∑ j:Axis,f i j:= by
    let g(z:Axis×Axis):= f z.1 z.2+f z.2 z.1; let p(x:Axis×Axis):= x.1<x.2; let P:=Finset.univ.filter p
    change ∑ i:PlaqAxes,g i.val=_; rw [← Finset.sum_subtype P _ g] -- inspect
    swap; · simp [P,p]
    unfold P; rw [Finset.sum_filter, Fintype.sum_prod_type]
    have he (x y:Axis): (if p (x,y) then g (x,y) else 0)=(if x<y then f x y else 0)+(if x<y then f y x else 0):= by unfold g p;split_ifs <;> simp
    change (∑ i:Axis,∑ j:Axis, (if p (i,j) then g (i,j) else 0))= _; simp_rw [he, Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun i j:Axis=>if i<j then f j i else 0)]; simp_rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rcases lt_trichotomy i j with h'|rfl|h' <;> first|simp [h',h'.not_gt]|simp [h]

local notation "H"=> Hair G
local notation "ℓ"=> Curly G
local notation "Ξ"=> G.ColorIndex
variable (χ:Lane)
def fireMask (χ: Lane): ℓ:= beadR χ fun z=>∑ i:PlaqAxes, flashVertex (z,i)
variable (δ:Cover→ G.Color)
def stepCloud (i:Axis)(z:Cover): ℓ:= ∑ j:Axis,∑ k:Ξ,glyph (com (sun (z-step i) i j k))*glyph (str δ ((z,j),k))
def changed (χ: Lane)(i:Axis):Lane:= nudged χ (step i)-χ
def cutoffShell: ℓ:= ∑ i:Axis,beadR (changed χ i) (stepCloud δ i)
def groundV (x:H):ℓ:= glyph (com (keyRow x))*glyph (str δ x)
def groundS : ℓ := beadR χ (fun z=>∑ i:Axis,∑ j:Ξ, groundV δ ((z,i),j))
lemma changed_point (i:Axis)(z:Cover): changed χ i z=χ (z-step i)-χ z:= by rw [changed,Finsupp.sub_apply,nudge]
lemma plus_maskR (A:Brush G): snap A (stroke (raised δ) (fireMask (G:=G) χ)) =-(beadR χ (fun z=>∑ i:PlaqAxes,Complex.ofReal (inner ℝ (curlL i.val.1 i.val.2 A z) (curlL i.val.1 i.val.2 (θ δ A) z)))):= by
    let T:=stroke (raised δ); let f(z:Cover):= ∑ i:PlaqAxes,flashVertex (G:=G) (z,i); let K:= ((snap A).toLinearMap ∘ₗ T.toLinearMap).restrictScalars ℝ; change K (beadR χ f)= _; rw [beadLm,← bead_neg]; apply congr_arg; funext z; change snap A (T _) =_; show _= -(∑ i:PlaqAxes, _); simp_rw [f,map_sum, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _=> (flash_rose δ (z,i) A).trans (by push_cast;rfl)
lemma smoke (A:Brush G)(x:H): snap A (glyph (str δ x))= Complex.ofReal (text (θ δ A) x):= by rw [str,com_text,snaps_blade,struck];rfl
lemma carbon (A:Brush G)(g:Fan G): snap A (glyph (com g))=Complex.ofReal (flatL A g):= by rw [com_text,snaps_blade];rfl
lemma full_maskK (A:Brush G): snap A (groundS χ δ)= beadR χ (fun z=> ∑ i:Axis,Complex.ofReal (inner ℝ (orderK i A z) (θ δ A (z,i)))) := by
    let L:ℓ→ₗ[ℝ] ℂ:= (snap A).toLinearMap.restrictScalars ℝ; change L (beadR χ _) = _; rw [beadLm]; apply congr_arg; funext z; change snap A (∑ j:Axis, ∑ k:Ξ, _) =_; simp_rw [map_sum,groundV,map_mul,smoke,carbon,reading,paint_norm, Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> (Complex.ofReal_mul ..).symm
lemma shell_mask (A:Brush G): snap A (cutoffShell χ δ)=∑ i:Axis, beadR (changed χ i) (fun z=>∑ j:Axis, Complex.ofReal (inner ℝ (curlL i j A (z-step i)) (θ δ A (z,j)))):= by
    rw [cutoffShell,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; let T:ℓ→ₗ[ℝ] ℂ:= (snap A).toLinearMap.restrictScalars ℝ; change T (beadR _ _) = _; rw [beadLm]; apply congr_arg; funext z; change snap A (stepCloud δ i z)=_; simp_rw [stepCloud,map_sum,map_mul,smoke,carbon,sun_at,paint_norm,Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=> (Complex.ofReal_mul ..).symm
end YM.PositionX.Braid
