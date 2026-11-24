import YM.PertExtension.OrbCovariance

/-! Passing from inversion-equivariant test potentials to the tree fluctuation
coordinates without physically dropping any curvature directions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.PertExtension.LatticePT
namespace Orbit
open MeasureTheory Filter YM.Lattice Set Real Metric Lattice Orb GaussianScore
open Function Finset
open scoped Topology BigOperators ContDiff Classical RealInnerProductSpace
variable {n : Side}{E : Type*} [AddCommGroup E] [Module ℝ E]

def Mirrors (B : Links (Per n) E):Prop:=∀ e, B (reflect e) = -B e

theorem all_loaded (h : Even n.val) {B : Links (Per n) E}(hb : Mirrors B) :
    ∃ A : Cotree n → E, ∀ z i j, Curl (variation A) z i j=Curl B z i j := by
    let K:=Multiplicative E
    let b (e:Trees n) := Multiplicative.ofAdd (B e.val.val)
    let u (e:Cotree n):= Multiplicative.ofAdd (B e.val.val)
    let A (e:Cotree n):= Multiplicative.toAdd (fresh b u e)
    have base (e:OEdge n): splitLink b u e=Multiplicative.ofAdd (B e.val):=by unfold splitLink; split <;> rfl
    have he (e:Edge (Site n)) :links b u e= Multiplicative.ofAdd (B e):= by
        rcases eR_spec e with he|he
        · change liftLinks _ e = _; rw [liftLinks,if_pos he,base]; rw [show (index e).val=e from he]
        by_cases hf:eR e=e; exact False.elim (no_fixed_edge h e (he.symm.trans hf))
        have hn := lift_flip h (splitLink b u) e
        have ht : eR (reflect e)=reflect e:= (eR_reflect ..).trans he
        have hb' := hb (reflect e); change B _= -B _ at hb';rw [reflect_reflect] at hb'
        rw [← inv_inj, ← hn,liftLinks,if_pos ht,base,hb'] -- patch
        change _= (Multiplicative.ofAdd (-(B _)))⁻¹
        rw [show (index (reflect e)).val=reflect e from ht]; exact (by change B (reflect e) = -(-(B ..)); simp)
    have hs (i:OEdge n) : Multiplicative.toAdd (splitLink 1 (fresh b u) i :K)=genJet A i:= by
        unfold splitLink genJet; split_ifs <;> rfl
    let t (x:Site n) := Multiplicative.toAdd (frame b x)
    have hv (e:Edge (Site n)) : Multiplicative.toAdd (aligned b u e) = variation A e := by
        rw [alignment h,links,liftLinks]; split_ifs <;> simp [show variation A (E:=E) e=(if eR e=e then genJet A .. else -genJet A ..) from rfl,hs] <;> tauto
    have hv' (x : Site n)(i:Axis) : variation A (x,i)= t x+B (x,i) - t (x+step i):=by
        rw [←hv];change t _+ Multiplicative.toAdd (links b u _) + -t _ = _; rw [he];exact (sub_eq_add_neg ..).symm
    exact ⟨A,by intro z i j; simp only [Curl,hv',show z+step i+step j=z+step j+step i by abel]; abel⟩
end Orbit
end YM.PertExtension.LatticePT
