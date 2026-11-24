import YM.LocalLTE.Hall.Receipt
import YM.Next.SCHEDULE.SlotPay
import YM.LocalLTE.Concert.Contact
/-!
# Any length known fixed. Genuine Wilson loop signals

Measured on path, real or imaginary projections later, arbitrary spike couplings also by scaling.
No dependence on torus size.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.G07 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums Next.Scheduling.Wages
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side} (B:BudgetPoint) (U:Config G n)(x:Site n)(l:Walk)(b d:ℕ)
variable {V α :Type}[DecidableEq V]{R:Census V}
open Animals ConnectedActivityE6 Blaze Brush
private lemma prox (y:Site n)(i:Step): separation y (y+i.vec)≤1:= by
    rw [separation_comm,separation,add_comm,add_sub_cancel_right,Step.vec]; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
private lemma process (G:Gauge) : Path.price (Path.tissue (G:=G) x l)=1 ∧ (Path.uses (Path.tissue (G:=G) x l)).length=l.length ∧
      (∀ i∈Path.uses (Path.tissue (G:=G) x l),separation x i.1 ≤ l.length) ∧ ∀ y∈ Lattice.visits x l,separation x y ≤ l.length:= by
  induction l generalizing x with
  | nil => simp [Path.tissue,Path.price,Path.uses,Lattice.visits]
  | cons a l ih =>
    obtain ⟨h,h',he,hy⟩:=ih (x+a.vec)
    have hx : (Path.single (G:=G) x a).size=1 ∧ (Path.single (G:=G) x a).links = [a.used x] := by
      unfold Path.single; split <;> exact ⟨rfl,rfl⟩
    have ha:= prox x a
    rw [Path.tissue,Path.price,h,hx.1, one_mul,Path.uses,hx.2]
    simp only [List.singleton_append,List.length_cons,h',Lattice.visits]
    refine ⟨trivial,trivial,fun i hi => ?_,fun z hz=>?_⟩
    · rcases List.mem_cons.mp hi with rfl|hg
      · cases a with
        | mk i b =>
          cases b
          · rw [show (Step.used _ _).1=x from rfl]; simp
          apply le_trans (b:=1) _ (Nat.le_add_left ..)
          simpa [Step.vec,Step.used,sub_eq_add_neg] using ha
      exact le_trans (separation_triangle x (x+a.vec) i.1) (by have := he i hg; omega)
    rcases List.mem_cons.mp hz with hz|hz; · simp [hz]
    exact le_trans (separation_triangle x (x+a.vec) z) (by have :=hy _ hz; omega)
-- L∞ b uniform all points. open coupling factor ANY.K. Reservation on OLD K.
variable {c:ℝ} (L:G.Mat →L[ℝ] ℝ)
def traceT := fun V:Config G n=> L (G.mat (Lattice.travel V x l))
lemma traceVal : traceT x l L=fun U : Config G n=> L (Next.Scheduling.Wages.Path.eval (Path.tissue x l) U):= by funext U; rw [traceT,Path.picture]
variable (hp:l.length ≤ b) (h:Lattice.stop x l=x) (hr:∀ u v:G.El,L (G.mat (u*v*u⁻¹))=L (G.mat v)) (he: ∀ x,‖L x‖ ≤ c*‖x‖) (hc:0≤c)
local notation "pv"=> traceT x l L
include hp h hr
lemma traceDuty : B.Regular (Animals.neighbors b x) (traceT x l L):=by
    have ht:LeftSmooth B.order pv:=(traceVal ..).symm ▸ (Path.soft (Path.tissue x l) _).postcomp L
    refine ⟨fun i j h=>?_,(show Continuous pv from L.continuous.comp (show Continuous (fun U:Config G n=>G.mat (Lattice.travel U x l)) by fun_prop)).measurable,?_,fun V _=>?_,fun V _ A l h=>ht.has h.le V A⟩
    · apply congr_arg (fun y=>L (G.mat y)); exact travel_local _ _ i j (agrees_mono h (fun i hi=> (neighbors_mem ..).2 ((process x l G|>.2.2.2 i hi).trans hp)))
    · intro f V; unfold traceT; rw [travel_gauge,h]; exact hr ..
    exact (ht [] (by simp) _).contDiffAt.of_le (show (↑(B.order:ℕ∞):WithTop ℕ∞)≤ ↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)
omit h hr
include he hc
def slotPay (G:Gauge)(c:ℝ)(b j p:ℕ):= c*(‖(1:G.Mat)‖*(1+(b:ℝ)*G.colorScale*(1+b)^p)^j)
lemma traceBound (a:List (Directions G n))(ha:a.length≤B.order)(hv:∀ i∈a, B.dirBound x i): ‖leftDerivs (traceT x l L) a U‖ ≤ slotPay G c b B.order B.power:=by
    unfold slotPay
    let T:= Path.tissue (G:=G) x l; let P:= G.colorScale*(1+(b:ℝ))^B.power; obtain ⟨h,hx,hy,hz⟩:=process x l G
    rw [traceVal]; erw [Work.G07.left_linear (Path.soft (Path.tissue x l) _) L ha]; have hG:= G.colorScale_pos; have ht:=B.threshold_le
    dsimp only; refine (he _).trans (mul_le_mul_of_nonneg_left ?_ hc)
    have hf : 0≤ P:=by unfold P; positivity
    apply le_trans (Path.bill T P hf U a ?_) _
    · intro i hi A hA; rw [G.colorMat_norm]; apply mul_le_mul_of_nonneg_left ((hv A hA i).trans ?_) hG.le
      rw [separation_comm]; refine (mul_le_of_le_one_left (by positivity) ht).trans (pow_le_pow_left₀ (by positivity) ?_ _); exact add_le_add le_rfl (by exact_mod_cast (hy i hi).trans hp)
    unfold T; rw [h,hx,one_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [mul_assoc _ _ ((1+(b:ℝ))^B.power)]; change (P*_)^_ ≤ (1+(b:ℝ)*P)^_
    have hh:P*l.length ≤ 1+(b:ℝ)*P:=by rw [mul_comm]; exact (mul_le_mul_of_nonneg_right (show (l.length:ℝ) ≤ b from by exact_mod_cast hp) hf).trans (by norm_num)
    exact (pow_le_pow_left₀ (by positivity) hh _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) ha)
-- joint Analytic germ step order arbitrary. chart coordinate. economical use exCost from bullet
variable (G)
omit hp he hc
open FrameBox Grove
lemma trestleT (c:ℝ)(hc:0 ≤ c) : ∃ M':ℝ,0≤M'∧ ∀ (n:Side)(x:Site n)(l:Walk)(L:G.Mat→L[ℝ]ℝ), l.length≤b→(∀ x,‖L x‖ ≤ c*‖x‖)→
       ∀ A:Directions G n, ‖A‖≤1 → Brush d M' 1 (traceT x l L ∘ FrameBox.Grove.soloV) A:=by
    obtain ⟨m,h,hm⟩:= Blaze.expCost G d 1; let e:= (1+m)*1; let r:=royalty G; have hv:0≤r:=zero_le_one.trans (royalty_ge G); have hu:0≤e:=by unfold e; positivity
    let v:= c*r*(1+b*(e*r))^d; refine ⟨v, (by unfold v; positivity),fun n x l L hp he A hx=>?_⟩
    let a:= soloV (G:=G) (c:=n); have hf: Mode a A d e:=by
       refine ⟨hu,fun i=>?_⟩; have hh:= hm (A i) ((norm_le_pi_norm _ _).trans hx)
       let B:(Directions G n)→L[ℝ] _:=ContinuousLinearMap.proj i
       have hB:‖B‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=> by rw [one_mul]; exact norm_le_pi_norm v i)
       have hg:= Brush.reading (x:=A) B hh hB -- adjust
       rw [one_mul] at hg; exact Blaze.thicken (f:=fun V=> a V i) hg
    have hA:= (Blaze.tour (U:=a) (w:=l) (o:=x) hf.pos hf.atLink) -- duplicated
    exact (((hA.report L (ContinuousLinearMap.opNorm_le_bound L hc he)).climb le_rfl (show l.length*(e*royalty G)≤ (b:ℝ)*(e*r) from mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (by positivity))).trim)
end YM.LocalLTE.Port
