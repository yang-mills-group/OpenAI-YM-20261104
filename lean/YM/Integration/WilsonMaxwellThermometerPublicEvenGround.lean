import YM.Integration.WilsonMaxwellThermometerVotedCurrency

/-! The grade-zero finite Galop faces after restoration of every genuine
engineering weight. They keep the entire complementary even upper field. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicEvenGround
open Function Set Filter Finset Spec Extraction Labels Maxwell Maxwell.Free
open XSpace XSpace.Structure1 XSpace.Cirrus XSpace.Normalize XSpace.Retirement XSpace.Photo XSpace.Graph3 XSpace.Rose
open WilsonMaxwellThermometerPublicGalop WilsonMaxwellThermometerPublicEvenSlope WilsonMaxwellThermometerChargedHeads
open WilsonMaxwellThermometerPositionCurrency WilsonMaxwellThermometerVotedCurrency
open scoped Classical BigOperators
variable {G:Gauge}(W:Initialize G){V:Normalize.Store G}(x:Sample 3)

theorem odd (F:Labels.Frame G 6)(v:F.Coeff):hinge 6 (sector F (head F v)) = -sector F (head F v):=by
  rw [summed,map_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases full:F.grades i=(6,3)
  · simp only [head,map_smul,reflection,full]
    change v i • (((-1:ℂ)^3) • arm F i) = -(v i • arm F i)
    rw [show (-1:ℂ)^3 = -1 by norm_num, neg_one_smul ℂ (arm F i),smul_neg]
  · simp [head,full]

theorem reading (p:Tags G 6 3)(S:Finset (Fin 3)):
    quotient W (V:=V) x p 0 S=cooked W V 6 x 0 (missing p S):=by symm;apply detail

theorem masked (simple:G.Simple)(a:Sec G 6)(ha:hinge 6 a = -a)
    (u v:Sec G 4)(S:Finset (Fin 3))(present:0∈S):
    let p:=missing (entered a u v) S
    hinge 6 ∘ p = Function.update p 0 (-p 0):=by
  let p:=missing (entered a u v) S
  have lo (t:Sec G 4):hinge 6 (up (by decide:4≤6) t)=up (by decide:4≤6) t:=
    Subtype.ext (AxesTangent.same_low simple t.val t.property)
  have fixedLower (t:Sec G 4)(P:Prop)[Decidable P]:
      hinge 6 (if P then up (by decide:4≤6) t else leaf G 6) =
        if P then up (by decide:4≤6) t else leaf G 6:=by
    split
    · exact lo t
    · exact hinge_leaf 6 G
  funext i
  fin_cases i
  · change hinge 6 (if (0:Fin 3)∈S then a else leaf G 6) =
        -(if (0:Fin 3)∈S then a else leaf G 6)
    rw [if_pos present,ha]
  · exact fixedLower u ((1:Fin 3)∈S)
  · exact fixedLower v ((2:Fin 3)∈S)

private theorem zero (z:ℂ)(h:z= -z):z=0:=by linear_combination (norm:=ring_nf) h/2

private theorem cancel (D:Point G 6 3)(p:Tags G 6 3)
    (h:D (Function.update p 0 (-p 0))=D p):D p=0:=by
  have neg: D (Function.update p 0 (-p 0)) = -D (Function.update p 0 (p 0)) :=
    (D.toLinearMap p 0).map_neg (p 0)
  rw [Function.update_eq_self] at neg
  exact zero (D p) (h.symm.trans neg)

theorem signed (stage:V.Meets W x.F 6)(p:Tags G 6 3)
    (flip:hinge 6 ∘ p=Function.update p 0 (-p 0)):cooked W V 6 x 0 p=0:=by
  apply cancel (cooked W V 6 x 0) p
  rw [←flip]
  calc
    _ = ((-1:ℝ)^0) • (cooked W V 6 x 0 p):=cooksV W V 6 x p 0 stage
    _ = _:=by rw [pow_zero,one_smul]
    
theorem blank (simple:G.Simple)(stage:V.Meets W x.F 6)(a:Sec G 6)(ha:hinge 6 a = -a)
    (u v:Sec G 4)(S:Finset (Fin 3))(present:0∈S):
    quotient W (V:=V) x (entered a u v) 0 S=0:=by
  rw [reading]
  exact signed W x stage _ (masked simple a ha u v S present)

theorem actual (simple:G.Simple)(stage:V.Meets W x.F 6)(b a:Sec G 6)(oddA:hinge 6 a = -a)
    (u v:Sec G 4)(S:Finset (Fin 3)):
    quotient W (V:=V) x (entered (b+a) u v) 0 S=quotient W (V:=V) x (entered b u v) 0 S:=by
  by_cases present:0∈S
  · let p:=missing (entered b u v) S
    have edit (h:Sec G 6):missing (entered h u v) S=Function.update p 0 h:=by
      funext i;fin_cases i <;>simp [p,missing,entered,XSpace.Graph3.trip,present]
    have delta:=blank W x simple stage a oddA u v S present
    simp only [reading,edit] at delta ⊢
    rw [(cooked W V 6 x 0).map_update_add,delta,add_zero]
  · have same:missing (entered (b+a) u v) S=missing (entered b u v) S:=by
      funext i;fin_cases i <;>simp [missing,entered,XSpace.Graph3.trip,present]
    simp only [reading,same]

/-- Every finite ordinary face, including the empty face, has its actual
comparable ground at the same upper book and lower reannouncement. -/
theorem original (simple:G.Simple)(stage:V.Meets W x.F 6)(F:Labels.Frame G 6)(H:Labels.Frame G 4)
    (b:F.Coeff)(u v:H.Coeff)(a:ℝ)(S:Finset (Fin 3)):
    let h:=pay F x a b
    let p:=sector F h-sector F (head F h)
    let t:=received x a (sector H u)
    let w:=received x a (sector H v)
    quotient W (V:=V) x (entered (received x a (sector F b)) t w) 0 S=
      quotient W (V:=V) x (entered p t w) 0 S:=by
  dsimp only
  rw [WilsonMaxwellThermometerVotedCurrency.actual F x]
  let y:=pay F x a b
  let f:=sector F y-sector F (head F y)
  have decomposed:f+sector F (head F y)=sector F y:=sub_add_cancel _ _
  have h:=actual W x simple stage f (sector F (head F y)) (odd F y)
    (received x a (sector H u)) (received x a (sector H v)) S
  rw [decomposed] at h
  exact h

end YM.Integration.WilsonMaxwellThermometerPublicEvenGround
end
