import YM.OPE.Compatible.Stream.Grouping
/-!
# Repeated factor gap carried on variational curvatures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
open Flight
variable {L:Side} {j k:ℕ} {η x U a B:ℝ} {A: Row (TypeFace 2) (TypeFace 2)} (S:Cross L (TypeFace 2) (TypeFace 2)) (P: Flight j k)
def lobe:= List.finRange 4
local notation "T"=> TypeFace 2
local notation "V"=> Fin lobe.length
local notation "W" => (List.get lobe)

def angleCut (S:Cross L (TypeFace 2) (TypeFace 2)) (B:Row T T)(P:Cross L T T)(i:Axis) := composeRows (net S (fineCompose B P)) (pathJet T [i])
def sling (P:Flight j k)(x:ℝ) (S:Cross P.L (TypeFace 2) (TypeFace 2)) (A:Row T T) := ∑ i:V, angleCut S (selectAxis A lobe i) (P.groundPsi x [W i]) (W i)
variable (R:Cross P.L T T)
def Covers (η x U :ℝ)(j k:ℕ):Prop:=∀ P : Flight j k, ∀ z:List Axis,z.length≤j-2→(groundPsi x P z).strip η (U/(P.L.val:ℝ)^(2+z.length))
variable (hη:0<η)(hp:Covers η x U j k)(hA:A.strip η a)(hb:R.strip η B)
include hη hp hA
lemma band {D:ℝ}(hR:R.strip η (U/P.L.val^2))(hj:∀ z:Axis,(pathJet T [z]).strip η D) :
    let b:=lobe.length*(Fintype.card (TypeFace 2):ℝ)^3*yieldW η*D*U^2
    (sling P x R A).strip η (b/P.L.val*a):=by
    intro b
    have hf(i:Axis):(P.groundPsi x [i]).strip η (U/P.L.val^3):= hp _ [i] (by simp only [List.length_cons,List.length_nil]; have := P.legal; omega)
    apply strip_mono (row_strips fun i: V=>cashCarry hη.le hR (paid_each lobe hη hA i) (hf (W i)) (hj (W i))) le_rfl; apply le_of_eq; rw [Fintype.card_fin]; unfold b; ring
include hb
lemma carpet (i:V): Whole (net R (fineCompose (selectAxis A lobe i) (P.groundPsi x [W i]))):=by
    have hs:= hp P [W i] (by have := P.legal; simp only [List.length_cons,List.length_nil]; omega)
    exact (Whole.flipped (show Whole R from ⟨η,B,hη,hb⟩)).prod ⟨η,_,hη,strip_fine hη.le (paid_each lobe hη hA i) hs⟩
lemma silence : (sling P x R A).read 0=0:=by unfold sling angleCut; rw [whole_region (fun i:V=> (carpet P R hη hp hA hb i).prod (jet_whole _ [W i])) (0:Momentum) (by unfold physical; simp)]; exact Finset.sum_eq_zero fun i _=> whole_cull_zero (carpet P R hη hp hA hb i) _
lemma sailed (hx:0<x)(ht:4≤k)(he:A.read 0=0){c f:Side}(g: f.val=c.val*P.L.val):
   let r:=P.visitRatio g
   (sling P x R A).acts c = (installed r R)ᵀ*A.acts f*installed r (P.psi x):=by
      intro r
      unfold sling angleCut; rw [acts_region (fun i:V=> (carpet P R hη hp hA hb i).prod (jet_whole _ [W i])),wholesale lobe hη hA f he (fun i=>List.mem_finRange _),Matrix.mul_sum,Matrix.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      let y:= selectAxis A lobe i; let z := [W i]; let V' := P.groundPsi x z; have hh:z.length≤ j-2:=by have := P.legal; simp only [z,List.length_cons,List.length_nil];omega
      have hw:= paid_each lobe hη hA i; have hh':= hp P z hh
      have hz:= strip_fine hη.le hw hh'
      change (composeRows (net R (fineCompose y V')) _).acts c=_
      rw [(carpet P R hη hp hA hb i).acts (jet_whole T z), net_action r (show Whole R from ⟨η,_,hη,hb⟩) (show Whole (fineCompose y V') from ⟨η,_,hη,hz⟩), installed_fine r hη.le hw hh']
      have h:= refund_period x hx ht P g z hh
      change (installed r R)ᵀ * ((y.acts f)*installed r (P.groundPsi x z))* motion T c z = (installed r R)ᵀ*((y.acts f)*motion T f z)*installed r (P.psi x)
      change _*installed r (P.psi x)=installed r (P.groundPsi x z)*motion T c z at h
      simp only [Matrix.mul_assoc,h]
end YM.Next.Free.Frequency
