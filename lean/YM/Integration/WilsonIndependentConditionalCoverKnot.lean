import YM.Integration.WilsonIndependentConditionalCoverFare
import YM.RegulatorIR.Budget.Knot

/-! A connected join on the ordinary cover. Each of its two internal sites
is summed at the same child before either contraction or symmetrization. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverKnot
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Tuple RegulatorIR.Budget.Packet
open Lattice Laurent Bloch Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open scoped Classical BigOperators
variable {X α:Type}{i j:ℕ}

def entry (K:Layer X X)(T:Packet X (i+1))(U:Packet X (j+1))(x:Tuple X (i+j))(y:X×X):ℝ:=
   T (Fin.cons y.1 (cutLeft x))*(K y.1 y.2*U (Fin.cons y.2 (cutRight x)))

theorem sum (K:Layer X X)(T:Packet X (i+1))(U:Packet X (j+1))(x:Tuple X (i+j))
    (hf:Summable (entry K T U x)):(∑' y,entry K T U x y)=knot K T U x:=by
  classical
  rw [hf.tsum_prod]
  change _=∑' a,T (Fin.cons a (cutLeft x))*∑' b,K ((Fin.cons a (cutRight (r:=i) (s:=j) x):Fin (j+1)→X) 0) b*
    U (update (Fin.cons a (cutRight x)) 0 b)
  apply tsum_congr;intro a
  rw [←tsum_mul_left]
  apply tsum_congr;intro b
  have h:update (Fin.cons a (cutRight x):Fin (j+1)→X) 0 b=(Fin.cons b (cutRight x):Fin (j+1)→X):=by
    funext t;refine Fin.cases ?_ (fun z=>?_) t <;> simp [Fin.cons_succ]
  rw [h];rfl

def weight (i j:ℕ):ℝ:=(1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ)

private theorem view (K:ropes Cover α α)(T U:Gen ℝ (Cloth α))(x:dock Cover α (i+j))(y:dock Cover α 2):
    rill K T U (i+j) i j x y=weight i j*entry K (T (i+1)) (U (j+1)) x (finTwoArrowEquiv (Cloth α) y):=by
  rw [rill_spell];unfold entry weight
  change _=_*(T (i+1) (Fin.cons (y 0) (x∘Fin.castAdd j))*(K (y 0) (y 1)*U (j+1) (Fin.cons (y 1) (x∘Fin.natAdd i))))
  rw [smul_eq_mul]
  ring

theorem raw (K:ropes Cover α α)(T U:Gen ℝ (Cloth α))(x:dock Cover α (i+j))
    (h:Summable (rill K T U (i+j) i j x)):
    ruins (rill K T U (i+j) i j) x=weight i j*knot K (T (i+1)) (U (j+1)) x:=by
  let e:=finTwoArrowEquiv (Cloth α)
  let t:=entry K (T (i+1)) (U (j+1)) x
  have ov:0<weight i j:=by unfold weight;positivity
  have hh:Summable (fun q=>weight i j*t (e q)):=h.congr (view K T U x)
  have hv:Summable (fun q=>weight i j*t q):=e.summable_iff.mp hh
  have ht:Summable t:=by
    simpa only [←mul_assoc,inv_mul_cancel₀ ov.ne',one_mul] using hv.mul_left (weight i j)⁻¹
  unfold ruins
  rw [←sum _ _ _ _ ht,←tsum_mul_left,←e.tsum_eq]
  exact tsum_congr (view K T U x)

theorem original [Fintype α] (K:ropes Cover α α)(T U:Gen ℝ (Cloth α))
    (p:Cover){J:berth α α ℝ 2 (i+j)}(paid:Paves p J (rill K T U (i+j) i j)):
    ruins (rill K T U (i+j) i j)=weight i j • knot K (T (i+1)) (U (j+1)):=by
  funext x
  exact raw K T U x (WilsonIndependentConditionalCoverFare.original paid x)

end YM.Integration.WilsonIndependentConditionalCoverKnot
