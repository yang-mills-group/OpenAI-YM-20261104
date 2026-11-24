import YM.Integration.WilsonIndependentSpoutTrueFiniteVacuum
import YM.Integration.WilsonIndependentSpoutCenteredRanks

/-! Every retained positive angular row of the nonlinear finite exit has the
actual older Mer sign, clock and coefficient. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFiniteExitRows
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalPositiveVacuum (value)
open WilsonIndependentSpoutUnshiftedPost (bank)
open WilsonIndependentConditionalRawVacuum (finite)
open scoped Classical BigOperators Matrix
variable {I J X:Type}[Fintype I][Fintype J][Fintype X]

def pulled (U:Matrix X (I⊕J) ℝ)(E:Pal ℝ X):Pal ℝ J:=
  fun e=>fade (plug:Matrix (I⊕J) J ℝ) (fade U (E e))

theorem withdrawn (U:Matrix X (I⊕J) ℝ)(E:Pal ℝ X)(fin:∀e,FiniteGen (E e)):
    projectZero (loom U (Blue.flash E))=Blue.flash (pulled U E):=by
  rw [plug_project,loom_fade U E fin,loom_fade _ _ (fun i=>fade_finite (fin i) U)]
  rfl

theorem expense (T:Pal ℝ X)(scope:shellK 2 T)(bare:T 0=0)(sym:∀e,Pure (T e))(C:Matrix X X ℝ):
    (∀e,FiniteGen (finite C T e))∧∀e,Pure (finite C T e):=by
  refine ⟨fun e=>finite_sum fun i _=>finite_stops (stops_abr C scope bare) i e,?_⟩
  intro e r
  change Smooth ((∑i∈Finset.range (3*e+1),abr C T i e) r)
  rw [Finset.sum_apply]
  exact Smooth.sum fun i _=>pure_abr C sym i e r

variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

theorem original (simple:G.Simple)(p:ℕ)(n:Side)
    (paid:WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=loose A m
    let S:=mStep A n m;let F:=repeatF S;let H:=freeForms A N (m+1)
    let Ñ:=XSpace.Bare.chart G;let b:=n*P.L;let V:=(story A Ñ N (m+1)).1 b
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    let T:=bank P n (C.bore G Z (sheet D) f) α V;let U:=panSlice G S F (extractV G S F (roam A N m n))
    let E:=finite (fillSlots (Woods G n) (FreeResolvent.covariance G S F H)) T
    ∀ e,0<e→e≤p→∀r,0<r→pulled U E e r= -mix β ((story A Ñ N m).1 n) e r:=by
  intro N m P S F H Ñ b V α β T U E
  have age:m<N:=by dsimp only [N,m];have:=f.ok;omega
  let ratio:=XSpace.Bare.chart_ratio G
  have hv:Interlace H V:=(old A Ñ simple ratio N (m+1) age).basis b
  have h₁:=WilsonIndependentSpoutPostedSchool.original C Z D f P n α V hv.lamp hv.shape
  have cost:=expense T h₁.2.1 h₁.1 h₁.2.2 (fillSlots (Woods G n) (FreeResolvent.covariance G S F H))
  have receipt:=(WilsonIndependentSpoutTrueFiniteVacuum.original C Z D f A s simple p n paid).2
  intro e he amount
  let Q:=mix β ((story A Ñ N m).1 n) e
  have bottom:=(old A Ñ simple ratio N m age.le).basis n
  have incoming:FiniteGen Q:=finite_shell (mix_length (A:=β) bottom.lamp) e
  have plus:Pure Q:=mix_pure bottom.shape e
  have negf:FiniteGen (-Q):=by simpa only [neg_one_smul] using finite_μ incoming (-1)
  have negp:Pure (-Q):=by intro r ρ x;change -Q r (x∘ρ)= -Q r x;rw [plus r ρ x]
  apply WilsonIndependentSpoutCenteredRanks.original (fade_finite (fade_finite (cost.1 e) U) _)
    negf (fade_pure (fade_pure (cost.2 e) U) _) negp
  intro x
  have val:=receipt e amount x
  change value (projectZero (loom U (Blue.flash E))) e x=
    value (orbC (precisionC G n (freeForms A N m))) e x -
      value (redo β (Blue.flash ((story A Ñ N m).1 n))) e x at val
  rw [withdrawn U E cost.1,redo_stern β bottom.lamp] at val
  have np:totalR (-Q)= -totalR Q:=by simpa only [neg_one_smul] using visible_μ incoming (-1)
  simp only [value,Blue.flash,coeff_mk,orbC,coeff_C,if_neg (Nat.ne_of_gt he),map_zero,sub_zero,zero_sub] at val
  rw [np,map_neg,map_neg]
  change _= -(MvPolynomial.eval x (totalR Q)-MvPolynomial.eval (0:Lawn (Woods G n)) (totalR Q)) at val
  change MvPolynomial.eval x (totalR (pulled U E e))-MvPolynomial.eval (0:Lawn (Woods G n)) (totalR (pulled U E e))=
    -MvPolynomial.eval x (totalR Q) - -MvPolynomial.eval (0:Lawn (Woods G n)) (totalR Q)
  rw [val];ring

end YM.Integration.WilsonIndependentSpoutFiniteExitRows
