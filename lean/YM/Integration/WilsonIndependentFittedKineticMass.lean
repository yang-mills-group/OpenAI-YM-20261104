import YM.Integration.WilsonIndependentFittedForwardLength
import YM.Integration.WilsonIndependentFittedRelativeClock

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedKineticMass
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open scoped BigOperators Classical
variable {G:Gauge}{h:ℕ}{F:Labels.Frame G h}

theorem powers (G:Gauge)(e:ℕ)(E:Credit):
    ∃C:Credit,∀t:WindowS G (e+1) E,∀i j:ℕ,i≤e→j≤e→
      ‖coeff i ((relativeF t.robe.draws t.robe.paid t.n t.base t.span)^j)‖≤C.buy t.Age:=by
  let S:=(Finset.range (e+1))×ˢ(Finset.range (e+1))
  let P (k:ℕ×ℕ)(C:Credit):Prop:=∀t:WindowS G (e+1) E,
    ‖coeff k.1 ((relativeF t.robe.draws t.robe.paid t.n t.base t.span)^k.2)‖≤C.buy t.Age
  have one:∀k∈S,∃C:Credit,P k C:=by
    rintro ⟨i,j⟩ hij
    have hi:= Finset.mem_range.mp (Finset.mem_product.mp hij).1
    let B (t:WindowS G (e+1) E)(n):=relativeF t.robe.draws t.robe.paid n t.base t.span
    obtain ⟨d,C,_,paid⟩:=clipped_pow (WindowS.payments G (e+1) E) (i:=i)
      (p:=fun t:WindowS G (e+1) E=>B t t.n) (q:=fun t:WindowS G (e+1) E=>B t t.N)
      j (fun l hl=>ascend G (e+1) l E (by omega))
    refine ⟨⟨d,max 1 C,le_max_left ..⟩,fun t=>?_⟩
    exact (paid t).main.trans (mul_le_mul_of_nonneg_right (le_max_right ..)
      (pow_nonneg (zero_le_one.trans t.warm) _))
  obtain ⟨C,fees⟩:=uniformPays (P:=P) S one
    (fun i _ _ _ less paid t=>(paid t).trans (less _ t.warm))
  exact ⟨C,fun t i j hi hj=>fees (i,j) (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩) t⟩

theorem original (G:Gauge)(h e:ℕ)(E:Credit)(F:Labels.Frame G h):
    ∃C:Credit,∀(t:WindowS G (e+1) E)(d:Verse F)(A:ℝ),0≤A→
      (∀j≤e,∀a:Alma F,‖coeff j (d a)‖≤A)→∀j≤e,∀a:Alma F,
      ‖coeff j (music (relativeF t.robe.draws t.robe.paid t.n t.base t.span) d a)‖≤C.buy t.Age*A:=by
  obtain ⟨C,paid⟩:=powers G e E
  let c:ℝ:=((e+1:ℕ):ℝ)*2
  let V:=(pur c).prodC C
  refine ⟨V,fun t d A positive input j hj a=>?_⟩
  let r:=relativeF t.robe.draws t.robe.paid t.n t.base t.span
  have hr (i l:ℕ)(hi:i≤e)(hl:l≤e):twain (C.buy t.Age) 0 (coeff i (r^l)) (coeff i (r^l)):=
    twain.one _ _ le_rfl (paid t i l hi hl)
  have hx (l:ℕ)(hl:l≤e)(w:Alma F):twain (1*A) 0 (coeff l (d w)) (coeff l (d w)):=by
    rw [one_mul]
    exact twain.one _ _ le_rfl (input l hl w)
  have nn:0≤C.buy t.Age:=zero_le_one.trans (C.purchase t.warm)
  have actual:=(musicFund r r (C.buy t.Age) 1 A positive nn zero_le_one le_rfl hr d d hx j hj a).main
  apply actual.trans
  simp only [V,Credit.products]
  apply mul_le_mul_of_nonneg_right _ positive
  calc ((e+1:ℕ):ℝ)*(2*C.buy t.Age*1)=c*C.buy t.Age:=by unfold c;ring
       _≤_:=mul_le_mul_of_nonneg_right (pure_goal c t.Age) nn

end YM.Integration.WilsonIndependentFittedKineticMass
