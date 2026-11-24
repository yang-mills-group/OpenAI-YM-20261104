import YM.Integration.WilsonOriginalChargedRawJet

/-! Replacing the genuine raw pole by a lower initial coupling grade on the same registered finite and covered source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedSourceHead
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

private theorem movedAt {V:Type}{U:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](A:Gen V U){r h:ℕ}
    (hfit:h≤r)(j:ℕ) : moved r r A (j+h)=moved r (r-h) A j :=by
  by_cases k:r-h≤j
  · have k':r≤j+h:=by omega
    have n:r+(j+h-r)=r+(j-(r-h)):=by omega
    simp only [moved,if_pos k,if_pos k']
    exact congrArg (fun idx=>Blue.shine (A idx)) n
  · have k':¬r≤j+h:=by omega
    simp [moved,k,k']
private theorem movedZero {V:Type}{U:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](A:Gen V U){r h:ℕ}
    (hfit:h≤r){j:ℕ}(low:j<h) : moved r r A j=0 :=by
  simp [moved,show ¬r≤j by omega]

variable {G:Gauge}{ι:Type}[DecidableEq ι]{D:ι→ℕ}(o:ι){r h:ℕ}
variable (A:RG.Atom G r)(a:Knob (D o))(p:Chamber)(y:Cover)

theorem finite (hfit:h≤r)(n:Side)(j:ℕ) :
    ((source D o A a p r y).1 n) (j+h)=((source D o A a p (r-h) y).1 n) j :=by
  funext l v
  simp only [source,cn,shifted,skewV,revolve,tuftV,ply_v,volumeR,movedAt _ hfit]

theorem covered (hfit:h≤r)(j:ℕ) :
    (source D o A a p r y).2 (j+h)=(source D o A a p (r-h) y).2 j :=by
  funext l v
  simp only [source,cn,shifted,skewV,revolve,tuftV,ply_v,volumeR,movedAt _ hfit]

theorem before (hfit:h≤r)(n:Side)(j:ℕ)(low:j<h) :
    ((source D o A a p r y).1 n) j=0 ∧ (source D o A a p r y).2 j=0 :=by
  constructor <;> funext l v <;>
    simp [source,cn,shifted,skewV,revolve,tuftV,ply_v,volumeR,movedZero _ hfit low]

theorem radial (hfit:h≤r)(n:Side)(test:Case D) :
    readO test (source D o A a p r y) n =
      X^h * readO test (source D o A a p (r-h) y) n :=by
  apply PowerSeries.ext
  intro j
  rw [coeff_X_pow_mul']
  by_cases enough:h≤j
  · rw [if_pos enough]
    have values:=finite o A a p y hfit n (j-h)
    rw [Nat.sub_add_cancel enough] at values
    unfold readO
    simp only [Blue.flash,coeff_mk]
    apply congrArg totalR
    funext l v
    exact congrArg ((touch test {o}).toLinearMap) (congrFun (congrFun values l) v)
  · rw [if_neg enough]
    have values:=(before o A a p y hfit n j (by omega)).1
    unfold readO
    simp only [Blue.flash,coeff_mk]
    have empty:pPly test {o} ((source D o A a p r y).1 n) j=0:=by
      funext l v
      change (touch test {o}) (((source D o A a p r y).1 n) j l v)=_
      rw [values]
      exact map_zero _
    rw [empty]
    simp [totalR]

end YM.Integration.WilsonOriginalChargedSourceHead
