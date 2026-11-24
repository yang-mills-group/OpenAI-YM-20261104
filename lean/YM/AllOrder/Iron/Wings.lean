import YM.AllOrder.Iron.Gate
import YM.AllOrder.Iron.Rim
import YM.Next.STATIONARY.Films.ThinTrace
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
variable (i: G.ColorIndex)
open Wilson Precision
open Bloch Laurent Audience Push.Uniform
variable {α: Type}[Fintype α][DecidableEq α]{σ A:ℝ}
open Stationary
open scoped ComplexConjugate
lemma jam_eq {U V:CircM c α α}{F:Momentum→CompM α α}(hu: Jaunt U F 0)(hv:Jaunt V F 0): U=V:= by
 let R:= Bloch.rotations c α; have h: U*R=V*R:=by
    ext i ⟨p,j⟩; change (U *ᵥ (fun i=>R i (p,j))) i=(V*ᵥ (fun i=>R i (p,j))) i; rw [show (fun i=>R i (p,j))= tune p (Pi.single j 1) from funext fun i=>coef_wave .., hu _ _ (rolls.refl _),hv _ _ (rolls.refl _)]
 let Z:= (((c.val:ℂ)^4)⁻¹ • star R)
 have hz : R*Z=1 := by
    unfold Z R; rw [Matrix.mul_smul,rotations_gram,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (side_ne _)),one_smul]
 simpa only [Matrix.mul_assoc,hz,Matrix.mul_one] using congr_arg (· * Z) h
lemma lens (N : Funds (Co c α)){F:Momentum→ CompM α α}(h:∀ i j,Firm σ A (fun p=>(F p)⁻¹ i j)) (hf : Jaunt (approached N) F 0) (hx:IsUnit N.det) : Capped c Prod.fst Prod.fst (σ/4) (royalty σ A) N⁻¹:= by
   have ht:= cash_safe (U:=fun _:Corn (Fin 1)=>N) hx; have hu:= hf.backway ht; have he:= card_flip (U:=fun _:Corn (Fin 1)=>N) hx;
   change approached N⁻¹=(approached N)⁻¹ at he; rw [jam_eq hu (foil_germ h)] at he -- edit
   intro i j; rw [← Real.norm_eq_abs, ← Complex.norm_real]; have e: (↑(N⁻¹ i j):ℂ)=foil (fun p=>(F p)⁻¹) c i j:= congr_fun (congr_fun he i) j; rw [e]; exact foil_fee h

lemma lens' {b : Type} [Fintype b] [DecidableEq b](X:b≃ Co c α)(N:Funds b){F:Momentum→CompM α α}(h:∀ i j,Firm σ A (fun p=>(F p)⁻¹ i j))(hx: IsUnit N.det)(hp:Jaunt (approached (repackM X X N)) F 0) : Capped c (Prod.fst∘X) (Prod.fst∘X) (σ/4) (royalty σ A) N⁻¹:= by
 have hQ:= lens _ h hp (by rw [repack_det]; exact hx); rw [←repack_scale_inv _ _ hx] at hQ; intro i j; convert hQ (X i) (X j) using 1; simp [repackM]; rfl

def haloCost (σ:ℝ) (P:Patch):= (2*(4*(P.L.val:ℝ))+3)*Real.exp (σ*3)
def trimCost (σ :ℝ) (P:Patch) := (16*P.radius+(1:ℝ))*Real.exp (σ*(P.radius*12+(1:ℝ)))
def rack (G:Gauge)(σ:ℝ) (P:Patch):= metric (σ/2) (Iron.count P.L G)
abbrev fee (G:Gauge)(η:ℝ)(P:Patch)(C₁:ℝ):= let V:=haloCost η P * trimCost η P * rack G η P; V*C₁*rack G (η/2) P*V*rack G (η/2/2) P
set_option maxHeartbeats 200000 in
lemma earn (hp:S.patch.Branches S.kernel G) (hc:0≤A)(he:0<σ) (μ:ℝ)(hμ:0<μ)(Q:Momentum→CompM (ParcelG G S.patch.L) (ParcelG G S.patch.L))
   (h:Poster σ Q)(hv:Freezer (slabW G S.patch.L).dual (slabW G S.patch.L) Q σ A)
   (hH: Jaunt (approached (repackM (clothe G S) (clothe G S) (medals S t p R μ (fedora S t) 1 1))) Q 0)
   (hB:Shell S t p R (1:Config G c) (1:Joint G c f)) {H Y L:ℝ} (hS : R.Bounds p H Y L)(h0:IsUnit (hessian F t p R 0 0).det) :
    let u:=σ/4
    let C:= door A S.patch.L σ
    Capped c (fun i:Key F G=> S.ratio.parent i.1.val.1) (fun i:Key F G=> S.ratio.parent i.1.val.1) (u/2/2/2) (fee G u S.patch (royalty σ C)) (hessian F t p R 0 0)⁻¹:= by
   intro u C; let h:=h; let Z:=S.patch; let F₀:=clothe G S; let v:= addressJ S (G:=G); obtain ⟨hj,hq⟩:= slab_model F t μ (graces F) h0 hB hμ hp hS (grace_lift F) (grace_turn F); rw [hj]; let Q₀:=medals S t p R μ (fedora S t) 1 1; let p':= fun i:Key F G=>S.ratio.parent i.1.val.1; let C':= royalty σ C;
   have hu:0<u:=by unfold u; positivity
   have hk: Capped c v v u C' Q₀⁻¹:= lens' F₀ _ (door_supply h he hc hv) hq hH
   let X:= shear (fedora S t) (1:Joint G c f); let T:= graces F (G:=G)
   have hT : Capped c p' v u (haloCost u Z) T:= by convert closing hu.le (by positivity : (0:ℝ)≤ 2 * (4*(S.ratio.count.val:ℝ))+3) 3 (a:=p') (b:=v) (fun i j=> grace_bond F i j) using 1; simp [haloCost,Z]; rfl
   have hX : Capped c v v u (trimCost u Z) X:= by convert closing hu.le (by positivity : (0:ℝ) ≤16*Z.radius+1) (Z.radius*12+1) (M:=X) (b:=v) (a:=v) (fun i j=> ⟨(shear_pay (t:=t) hp i j).2,(shear_pay hp (t:=t) i j).1⟩) using 1; unfold trimCost; push_cast; rfl
   have hx : 0≤trimCost u Z:=by unfold trimCost; positivity
   have hy : 0≤haloCost u Z:=by unfold haloCost; positivity
   have hY := crowd S (G:=G); let A0:= haloCost u Z* trimCost u Z* rack G u Z
   have hP(s:ℝ)(hs:0<s):0≤ rack G s Z:= mul_nonneg (by positivity) (count_pos (half_pos hs)).le
   have hA:0≤A0:= mul_nonneg (mul_nonneg hy hx) (hP u hu);
   have hg : 0≤C':= by unfold C' royalty C door; positivity
   have hr: Capped c p' v (u/2) A0 (T*X):= Capped.bond (hT.mono (by linarith) hy) (hX.mono (by linarith) hx) (half_pos hu) hY hy hx;
   have hs : Capped c p' v (u/2/2) (A0*C'*rack G (u/2) Z) (T*X*Q₀⁻¹):= Capped.bond (hr.mono (by linarith) hA) (hk.mono (by linarith) hg) (half_pos (half_pos hu)) hY hA hg
   exact Capped.bond (hs.mono (by linarith) (mul_nonneg (mul_nonneg hA hg) (hP _ (half_pos hu)))) (hr.flip.mono (by linarith) hA) (by linarith) hY (mul_nonneg (mul_nonneg hA hg) (hP _ (half_pos hu))) hA
end YM.AllOrder.Iron
