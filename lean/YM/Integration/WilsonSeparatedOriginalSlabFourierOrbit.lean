/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import Mathlib.Analysis.Fourier.AddCircleMulti

/-! A genuine half-period translation gives each power of the joint Fourier score. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierOrbit
open MeasureTheory UnitAddTorus Function Set
open scoped Topology BigOperators Classical
variable {J:Type*}[Fintype J]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def wrap (x:J→ℝ): UnitAddTorus J:=fun i=>(x i:UnitAddCircle)
def shift (k:J→ℤ)(i:J):J→ℝ:=Pi.single i (1/2/((-(k i):ℤ):ℝ))
def moved (z:UnitAddTorus J)(F:C(UnitAddTorus J,ℂ)):C(UnitAddTorus J,ℂ):=
  ⟨fun x=>F (x+z)-F x,(F.continuous.comp (continuous_id.add continuous_const)).sub F.continuous⟩
def copies (z:UnitAddTorus J):ℕ→C(UnitAddTorus J,ℂ)→C(UnitAddTorus J,ℂ)
  | 0,F=>F
  | n+1,F=>copies z n (moved z F)

private theorem flip (k:J→ℤ)(i:J)(he:k i≠0)(x:UnitAddTorus J):
    mFourier (-k) (x+wrap (shift k i))= -(mFourier (-k) x):=by
  change (∏j:J,fourier ((-k) j) ((x+wrap (shift k i)) j))=-(∏j:J,fourier ((-k) j) (x j))
  let a (j:J):=fourier ((-k) j) ((x+wrap (shift k i)) j)
  let b (j:J):=fourier ((-k) j) (x j)
  change ∏j:J,a j=-(∏j:J,b j)
  rw [←Finset.mul_prod_erase _ a (Finset.mem_univ i),←Finset.mul_prod_erase _ b (Finset.mem_univ i)]
  have hi:a i= -b i:=by
    simpa only [a,b,wrap,shift,Pi.single_eq_same,Pi.add_apply,Pi.neg_apply] using
      (fourier_add_half_inv_index (neg_ne_zero.mpr he) zero_lt_one (x i))
  have same: ∏j∈Finset.univ.erase i,a j=∏j∈Finset.univ.erase i,b j:=by
    apply Finset.prod_congr rfl; intro j hj
    simp [a,b,wrap,shift,Pi.single_eq_of_ne (Finset.mem_erase.mp hj).1]
  rw [hi,same,neg_mul]

private theorem regular (F:C(UnitAddTorus J,ℂ))(k:J→ℤ): Integrable (fun x=>mFourier (-k) x *F x) volume:=by
  rw [←integrableOn_univ]; exact ((mFourier (-k)).continuous.mul F.continuous).continuousOn.integrableOn_compact isCompact_univ

theorem first (k:J→ℤ)(i:J)(he:k i≠0)(F:C(UnitAddTorus J,ℂ)):
    mFourierCoeff (moved (wrap (shift k i)) F) k = (-2:ℂ)*mFourierCoeff F k:=by
  let z:=wrap (shift k i)
  let G:C(UnitAddTorus J,ℂ):=⟨fun x=>F (x+z),F.continuous.comp (continuous_id.add continuous_const)⟩
  have translated: (∫ x:UnitAddTorus J,mFourier (-k) x*G x)=-(∫ x:UnitAddTorus J,mFourier (-k) x*F x):=by
    have same:= integral_add_right_eq_self (μ:=volume) (fun x:UnitAddTorus J=>mFourier (-k) x*F x) z
    simp_rw [show ∀x:UnitAddTorus J,mFourier (-k) (x+z)= -mFourier (-k) x from flip k i he,neg_mul,integral_neg] at same
    exact neg_eq_iff_eq_neg.mp same
  change (∫x:UnitAddTorus J,mFourier (-k) x*(G x-F x))= -2*(∫x:UnitAddTorus J,mFourier (-k) x*F x)
  simp_rw [mul_sub]; rw [integral_sub (regular G k) (regular F k),translated]; ring

theorem powers (n:ℕ)(k:J→ℤ)(i:J)(he:k i≠0)(F:C(UnitAddTorus J,ℂ)):
    mFourierCoeff (copies (wrap (shift k i)) n F) k=(-2:ℂ)^n *mFourierCoeff F k:=by
  induction n generalizing F with
  | zero=>simp [copies]
  | succ n ih=>rw [copies,ih,first k i he,pow_succ]; ring

end YM.Integration.WilsonSeparatedOriginalSlabFourierOrbit
