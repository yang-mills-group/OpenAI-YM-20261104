import YM.MS.Swirl.Resolute
import YM.WilsonComparison.Finite.Native

/-!
# Fourier bridge at the Wilson vertices of PhysicalSum

The cover stencils may wrap; **no** support/separation assumption for this
finite-volume equality. All modes and labels, also at zero and Nyquist. This
identifies the `Bulk` projection on the unmarked translation sum (different
from simply pinning that vertex!) and `Anchor` on marked stencils, after
phase-shift to base-point convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Lattice Bloch Precision
open MS MS.Landau MS.Cylinder MS.Cylinder.Lab MS.Koszul MS.Native
open MS.Orbit MS.Swirl MS.Swirl.Near MS.Tone MS.Fleet MS.Plane
open MSBar MSBar.Bric MSBar.Loft MSBar.Inlay
open Bric.Coil
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {K : ChartRatio G}
local notation "P" => FixedMode G n

local notation "R" => Complex.ofRealHom

abbrev fourierL := lantern (A:=FixedMode G n) Finset.univ (fun i j=> FT j i)
lemma fourier_cyl (x : Dot G (Site n)) : fourierL x.val= shade (fun i j=> FT j i) x:= by
  rw [tinted _ x (show Cylinder.Uses (↑(Finset.univ : Finset P) : Set P) x.val from ?_)] -- namespace
  rw [Finset.coe_univ]; exact Cylinder.Uses.entire _
lemma symbols_encode (x : Cutis.Winter.LightQ G n ℂ) : symbols σbranch ℂ (encodeMomentum x)=fourierL (siteSymbol x) := by
  let e:=tagPosition G (Site n)
  let L:=fun F=> symbols σbranch ℂ (encodeMomentum (G:=G) (n:=n) F)
  have he (x: Heave G (Edge (Site n)) (Site n) ℂ) (a:LegPosition G (Site n)) :
      Koszul.D (e a) (siteSymbol x)=siteSign a • (siteSymbol (Coil.D a x)):= by
    ext l; simp only [Koszul.at_D,siteSymbol_read,List.map_cons, List.prod_cons,Pi.smul_apply,smul_eq_mul];
    change _ * x ((e.symm (e a)) :: _) = _
    rw [e.symm_apply_apply]; unfold siteSign; rw [mul_assoc]; rfl
  change L x= _; ext l; induction l generalizing x with
  | nil=> rw [show L x []=x [] from rfl]; change _=(siteSymbol x) []; rw [siteSymbol_read]; simp
  | cons i l IH=>
    rw [D_eval i (fourierL (siteSymbol x)), lantern_drop, D_eval i (L x)]
    change symbols σbranch ℂ (Coil.D i (shot _ _ legalChange x)) l= _
    rw [shot_D,Coil.drip_apply, map_sum,map_sum]
    simp_rw [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    symm; rw [← Equiv.sum_comp e _]; refine Finset.sum_congr rfl fun y _=>?_
    change FT (e y) i * fourierL (Koszul.D _ (siteSymbol x)) l=_* L (Coil.D y x) l; rw [he, map_smul, IH]; change FT (e y) i*(siteSign y * _)=(siteSign y* FT (e y) i)*_
    ring

-- single branch Fourier costs
lemma armFee (a : P) (j : LightMode G Cover) :
    FT (post (wrap n) j) a= lace (addr a) * paywave (addr a) j := by
  obtain ⟨k,p⟩:=a; obtain ⟨r,x⟩:=j; dsimp only [FT,post]; by_cases h:r=k
  · subst k; rw [if_pos rfl]; rw [show paywave _ _= _ from pw r x (Coord p),Tone.rightadd]
    rw [Tone.rights (Coord p) (embed x), dual_cell]; calc
      _ = cell p (wrap n x) * (weightψ (r,Coord p)*lace (r,Coord p)):=by rw [lace_,mul_one]
      _ = _ := by rw [mul_comm (lace _)]; unfold addr weightψ; ring
  rw [if_neg h,show paywave _ _=0 from not_not.1 (mt (Tone.in_light _ _) (Ne.symm h)),mul_zero]

lemma no_anchor (x : Dot G Cover) (l : List P) : fourierL (enters n x) l=
    sleeve lace (Tone.run x) (Orbit.stage l) := by
  change fourierL (shown n x).val l=_; rw [fourier_cyl]; unfold shown transport; rw [study]
  have hv (a j) := armFee (G:=G) (n:=n) a j
  change shade (fun (i:P) j=>FT (post (wrap n) j) i) x l=_; induction l generalizing x with
  | nil=> rw [shade_nil,sleeve_here]; simp [Orbit.stage,hook,Tone.run]
  | cons i l IH=>
    obtain ⟨s,hs⟩:= fromCyl x
    rw [deriv_lum _ _ x hs]; unfold Tone.run; rw [sleeve_here,show Orbit.stage (i::l)=addr i::Orbit.stage l from rfl,deriv_lum _ _ x hs, Finset.mul_sum];
    refine Finset.sum_congr rfl fun j _=>?_; rw [IH _, sleeve_here,hv]; unfold hook Tone.run; rw [List.map_cons,List.prod_cons]; ring

lemma with_anchor (x : Dot G Cover) (c A : Cover) : fourierL (enters n (Shift (A+c) x))=
    Mark_T G n A c x := by
  rw [← shift_add]; change _= anchor G n A (frameL c (Tone.run x)); rw [vFrame, eFrame];
  ext l; rw [spell_anchor,lodg,no_anchor,sleeve_here,sleeve_here, Tone.movement]; unfold Orbit.be; rw [Tone.rights]; ring
lemma pinned (x : Dot G Cover) (c : Cover) (l : List P) : fourierL (enters n (Shift c x)) l=
    Φa c (net l)*fourierL (enters n x) l := by
  nth_rw 1 [← add_zero c]; rw [with_anchor]; change anchor _ _ c (frameL 0 _) _=_; rw [eFrame,chase_now,no_anchor,Orbit.point]
lemma extensive (x : Dot G Cover) : fourierL (docket n x)= Bulk G n (sleeve lace (Tone.run x)) := by
  have he : docket n x = ∑ i:Site n, enters n (Shift (Lattice.lift i) x) := by
    change (sumHome (transport (wrap n) x)).val=_; rw [total_uses,sum_stack]; refine Finset.sum_congr rfl fun i _=> ?_; symm
    change (transport _ (Lab.Shift _ x)).val= (Lab.Shift _ _).val; rw [trans_shift,wrap_lift]
  rw [he,map_sum]; ext l; rw [Finset.sum_apply,bulkZ]; simp_rw [pinned,Φa,wrap_lift,← Finset.sum_mul]
  split_ifs with ht
  · simp_rw [ht, cell_origin, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]; rw [no_anchor, Orbit.point]; congr 1; simp [brightness] -- care volume
  have hb: (∑ i : Site n, cell i (net l))=0 := by simp_rw [fun i : Site n=> cell_duality i (net l)]; exact sum_cell ht
  rw [hb, zero_mul]

-- Rank levels commute to kernels of exact degree
open MS.Native.Wilsonian Odom
variable (hk:LocalRatio K)
lemma rank_wind {A L B:Type} [CommRing A] [CommRing L] {p:B→Bool} (f:A→+*L) (x:Coil p A) (k:ℕ) : rankn k (Wind p f x)=Wind p f (rankn k x) := by
  ext l; rw [blows,blows,seep_read, rankn_read,seep_read,rankn_read]; split_ifs <;> simp

/-- Complete site log after homogeneity expansion at unit lattice spacing,
  including *both* Wilson and Haar powers and the `1/2` on bulk.
  Includes the quadratic term at index zero! Remove exactly once for Gaussian contraction. -/
def logAlphabet (hk:LocalRatio K) (n:Side) (i:ℕ) : Cutis.Winter.LightQ G n ℝ :=
  (2:ℝ)⁻¹ • (-rankn (i+2) (Rack G n K hk).main + rankn i (Rack G n K hk).ash)
lemma send_unscaled (F : Dot G Cover) : SendB G n true F= (2:ℂ)⁻¹ • fourierL (docket n F) := by rw [extensive]; rfl
lemma priceRank (x:ℕ) : symbols σbranch ℂ (encodeMomentum (Wind ø R (logAlphabet hk n x))) =
    SendB G n true (core G x) := by
  rw [symbols_encode,send_unscaled]; unfold logAlphabet
  have he : (Complex.ofRealHom ((2:ℝ)⁻¹))=(2:ℂ)⁻¹ := by simp
  rw [Wind_smul,map_smul,map_smul,he]
  congr 2
  rw [core,Pi.add_apply,MS.Book.levels,MS.Book.levels,add_zero]
  simp_rw [map_add,← map_neg (rankn (x+2)), ← rank_wind, siteSymbol_rank, site_action hk, haar_action hk]
  rw [show docket n (MS.Book.model _ (Wilsonian.W G)) = MS.Book.mask _ (docket n (Wilsonian.W G)) from MS.Book.enterShim true n ((x:ℤ)+2),
    show docket n (MS.Book.model _ (Wilsonian.H G)) = MS.Book.mask _ (docket n (Wilsonian.H G)) from MS.Book.enterShim true n (x:ℤ)]
  norm_cast
end YM.WilsonComparison.Finite
