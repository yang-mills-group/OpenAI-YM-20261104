import YM.RG11Proof.Fields.Elevate
import YM.Pert.Triangle.End

/-!
# Ruler across all larger horizons from the reduced continuum triangle

Uses the nonzero independent *reduced diagnostic* (binding of profile/cTest
sign) and kills ANY legal field shift about actual free on-shell, not just a
further restricted scalar normalization. Constructs an explicit finite linear
meter through any horizon ≥6 to which that free input is lifted, dividing by
cTest exactly. Slope premises in the application are only on order-one of
the FULL tested report on that lifted input in each intended prescription (bind
BRST lifts and connected/moment convention carefully); no RG05 readout inverse
bounds used. Those first coefficients remain an independent *diagram/physical*
obligation; baseline does not infer their values from the reduced diagnostic.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.Pert YM.RG11.Jets Function Set Labels Maxwell Position Extra.FD
open Triangle
open PertExtension.Position (Mark)
open scoped Classical BigOperators
variable {G:Gauge} {F:Frames G} (hg:G.Simple) {d:ℕ} (h:6 ≤ d)

/-- Fixed orientation/triple. -/
def triple (F:Frames G):Fin 3→E F d:= up F h ∘ basic F

include hg in
theorem vanishes (x:Points 3) (hx:x∈conf 3)(k:Fin 3)(D:Buffer F d):
    visible F d x (update (triple h F) k (D.val (triple h F k))) = 0 := by
  rw [writes_pair]
  let t:=triple h F
  let f:= fun i=>writes F d (update t k (D.val (t k)) i)
  have hR i (hi:i≠0):reversePol G (f i)=f i:=by
    have hw (i:Fin 3)(hi:i≠0): t i ∈ lower F 4 d := by
      obtain ⟨v,hv⟩:=(show basic F i∈LinearMap.range (up F (d:=6) (e:=4) (by omega)) by rw [staircase]; exact lower_basic F i hi)
      unfold t triple; rw [comp_apply,←hv,up_up,←staircase _ (by omega)]
      exact ⟨v,rfl⟩
    have hs := hw i hi
    have hj : update t k (D.val (t k)) i ∈ lower F 4 d := by
      by_cases he:i=k
      · subst k; rw [update_self]; exact D.property.2.1 4 (by omega) _ hs
      rw [update_of_ne he]; exact hs
    obtain ⟨v,hv⟩:=(show update t k (D.val (t k)) i∈LinearMap.range (up F (d:=d) (e:=4) (by omega)) by rw [staircase]; exact hj)
    let y:= up F (d:=6) (e:=4) (by omega) v
    have he : y∈ lower F 4 6:= (staircase F (d:=6) (e:=4) (by omega)) ▸ (show y∈LinearMap.range (up ..) from ⟨v,rfl⟩)
    have hh:f i=writes F 6 y:=by unfold f; rw [←hv, up_write]; exact (up_write F (by omega) v).symm
    rw [hh]; exact low_reversal hg F he
  change Wick.moment G x f = 0
  by_cases hk:k=0
  · apply ordinary_kills hg hx f _ hR
    · intro i hi; subst k; unfold f t; rw [update_of_ne hi, triple, comp_apply, up_write]; exact write_minus F i hi
    subst k
    obtain ⟨v,hv⟩:=(show D.val (t 0)∈LinearMap.range (up F h) by rw [staircase]; exact up_buffer F D h _)
    unfold f; rw [update_self,←hv,up_write]; exact writes_through F 6 _
  apply ordinary_kills_even hg F hx f _ hR
  unfold f; rw [update_of_ne (Ne.symm hk)]; exact up_write ..

include hg in
theorem no_read (f : Test 3)(k:Fin 3)(D:Buffer F d):
    wickReading F d f (update (triple h F) k (D.val (triple h F k)))=0 :=by
  change f.applyTo _ = _
  rw [Test.apply_eq f (P:=fun _=>0) (fun _ hx=>vanishes hg h _ hx k D)]; simp [Test.applyTo]

--- finite scalar meter
variable (B:Basis F d)
abbrev census := Fin 3→B.J
def price (w:census B):ℂ:= (∏ i,B.b.equivFun (triple h F i) (w i)) / cTest G
def take (w:census B) : Fields.point B:=⟨⟨3,price h B w • profileChoice⟩,w⟩

-- Auxiliary complex reading that is ℂ-multilinear in the fields and complex
-- scalar in our Test convention.
lemma meter_read (f : Test 3→MultilinearMap ℂ (fun _:Fin 3=> E F d) ℂ)
   (hξ : ∀ z v,f (z • profileChoice) v=z * f profileChoice v):
    ∑ w:census B,(f (take h B w).1.test (fun i=>B.b (w i))).re=(f profileChoice (triple h F)/cTest G).re := by
  simp_rw [take,hξ,price,div_eq_mul_inv]
  conv_rhs=> arg 1; lhs; rw [←funext fun j=>B.b.sum_equivFun ((triple h F) j)]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ,Finset.sum_mul,Complex.re_sum]
  refine Finset.sum_congr rfl ?_; intro w _; rw [MultilinearMap.map_smul_univ,smul_eq_mul, mul_right_comm]

-- Adapted actual `RulerTest` for any tested coefficient array. The needed
-- response is stated as equality on the profileChoice with *triple labels*;
-- array on all places and the one response must come from the same system.
-- Includes every tested basis-place coefficient at those scaled profiles
-- (only to order one) and does not require a formula at unspecified locations.
def probeRuler (F : Frames G)(hg:G.Simple){d :ℕ} (h:6 ≤ d)(B:Basis F d)
   (A:ArrayAt B.J ℝ form) (hA : ∀ v,constantCoeff (A v)=rowZero B v)
   (T : Test 3→MultilinearMap ℂ (fun _:Fin 3=> E F d) ℂ)
   (hT : ∀ w, tangent (A (take h B w)) = (T (take h B w).1.test (fun i=>B.b (w i))).re)
   (hξ : ∀ z v,T (z • profileChoice) v = z * T profileChoice v)
   (hu : T profileChoice (triple h F) = cTest G): RulerTest B.guard A:=by
  let m:= Fintype.card (census B)
  let κ:= Fintype.equivFin (census B)
  refine ⟨m,take h B ∘ κ.symm,∑ i:Fin m, LinearMap.proj (φ:=fun _:Fin m=>ℝ) i,?_,?_⟩
  · intro z
    rw [LinearMap.sum_apply]; simp_rw [LinearMap.proj_apply, hA,price_orbit,comp_apply]
    trans ∑ w:census B,(firstColumn B z.val (take h B w).1 (fun i=>B.b ((take h B w).snd i))).re
    · exact Equiv.sum_comp κ.symm (fun w=> (firstColumn B z.val (take h B w).1 (fun i=> B.b ((take h B w).snd i))).re)
    let f(v : Test 3):=firstColumn B z.val ⟨3,v⟩
    change ∑ w:census B,(f (take h B w).1.test (fun i=> B.b (w i))).re=0
    rw [meter_read h B f ?_,show f profileChoice (triple h F)=0 from ?_]
    · simp
    · -- hn needed, column_apply private. recreate? export it.
      unfold f; rw [column_apply]; exact Finset.sum_eq_zero fun i _=> no_read hg h profileChoice i (B.operates z)
    intro w v; unfold f; rw [column_apply,column_apply]; change (∑ j:Fin 3,(w • profileChoice).applyTo _)=_; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=> price_scale ..
  rw [LinearMap.sum_apply]; simp_rw [LinearMap.proj_apply,comp_apply, hT]
  rw [Equiv.sum_comp κ.symm (fun w=>(T (take h B w).1.test (fun i=>B.b (w i))).re),meter_read h B T hξ,hu,div_self]
  exact rfl
  exact (Triangle.finiteTest hg F).unscaledResponse
end YM.RG11.Fields
