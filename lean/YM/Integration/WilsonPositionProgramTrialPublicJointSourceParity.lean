import YM.Integration.WilsonPositionProgramTrialPublicJointGroundPortfolio

/-! Thermal parity for a single submitted marked field through the original normalized
Gaussian step. Its offset is its own incoming angular valence. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceParity
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open Matrix Function Finset Lattice Laurent Bloch Exterior Wilson Precision RG Filter Metric
open FreeResolvent Tree PowerSeries Next.Free
open scoped BigOperators Classical
variable {U V M:Type*}{G:Gauge}{c f:Side}

def Signed [Zero M](l:ℕ)(P:Pal M U):Prop:=∀e r,(e+l)%2≠r%2 → P e r=0

theorem faded [Fintype U][AddCommGroup M][Module ℝ M] {l:ℕ}{P:Pal M U}
    (head:Signed l P)(B:Matrix U V ℝ):Signed l (fun e=>fade B (P e)):=by
  intro e r miss
  funext x
  change fade _ _ _ _=_
  rw [fade,head e r miss]
  simp

theorem heated [Fintype U][AddCommGroup M][Module ℝ M] (l:ℕ)(C:Matrix U U ℝ)
    (D:Layers ℝ U)(old:∀a,PairP (D a))(P:Pal M U)(head:Signed l P):
    ∀j,Signed l (bul C D P j):=by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero=> intro e r miss;rw [bul_zero];exact head e r miss
    | succ j =>
      intro e r miss
      have zero (B:Matrix U U ℝ):ravel B D (bul C D P) j e r=0:=by
        apply ravel_zero
        intro a b x y i t ab xy it
        by_cases signed:x%2=(i+1)%2
        · exact Or.inr (ih b (by omega) y _ (by omega))
        · exact Or.inl (old a x _ signed)
      have trace:ripple C (bul C D P j e) r=0:=
        ripple_zero_at C _ r (ih j j.lt_succ_self e (r+2) (by omega))
      simp only [bul_next,Pi.smul_apply,Pi.add_apply,trace,zero C,zero C.transpose,add_zero,smul_zero]

theorem turned [AddCommGroup M][Module ℝ M](l:ℕ){P:Pal M U}(head:Signed l P)
    {B:Cost}(unit:constantCoeff B=1)(even:evenC B):Signed l (Blue.mix B P):=by
  intro e r miss
  apply Finset.sum_eq_zero
  intro j small
  by_cases parity:(j+l)%2=r%2
  · rw [even_mul (even_pow even j) (even_pow (even_inv even unit) r) _
      (by have := Finset.mem_range.mp small; omega),zero_smul]
  rw [head j r parity,smul_zero]

private theorem cropped (P:Pal ℝ U)(p:PairP P):PairP (scrub P):=by
  intro e r miss
  rw [scrub]
  split
  · rfl
  exact p e r miss

theorem backdrop (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P:PChart G f)(p:PairP P):
    ∀j,PairP (xray S F H Q O P j):=by
  let M:=extractV G S F Q
  have fixed:PairP (casePW S O M P):=by
    apply pare_sub
    · apply pare_sub
      · exact faded (l:=0) (P:=sprig (unhaar O) 0) (fun e r a=>shine_dark (by omega)) _
      · exact faded (l:=0) (cropped (sprig (jointPen G S) 2) (fun e r a=>shine_dark (by omega))) _
    · exact faded (l:=0) (cropped P p) _
  exact order_parity _ fixed

theorem one [AddCommGroup M][Module ℝ M] (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P:PChart G f)(p:PairP P)
    (k l:ℕ)(X:Pal M (Woods G f))(head:Signed l X):
    Signed l (reed S F H Q O P k X):=by
  have heat:∀j,Signed l (srShade S F H Q O P X j):=
    heated l _ _ (backdrop S F H Q O P p) _ (faded head _)
  unfold reed
  apply faded
  intro e r miss
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _=>heat j e r miss

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceParity
