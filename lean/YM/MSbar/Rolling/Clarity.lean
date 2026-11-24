import YM.MSbar.Rolling.Rolling
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push Push.Uniform Exterior
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S: StepData c f}(B:Forest S.ratio)(i:S.Choices)(R T: PathData G)(p q: Clip)(ρ:fieldDir G c 1→AxisChart G B)
open Work.F03
local notation "∆"=> fderiv ℝ
local notation "P"=> uncurry (tested B i p R)
local notation "C₀"=> priced B i p R
local notation "W"=> paint B G
local notation "V"=> fieldDir G c 1
local notation "X"=> Positions (Primary c G)
local notation "Y"=> Positions (Key B G)
local notation "N"=> Positions (Primary f G)
local notation "H"=> Positions (Joint B G)
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "Ψ"=> (tint G)
abbrev height (n:Side)(p:Clip)(R:PathData G) (x:Positions (Primary n G)) := Tensor.diagonal (Tensor.coeff (main n p R) 2 0) ((tint G _) x)
noncomputable def relayB (G:Gauge) : Positions (Joint B G)→L[ℝ]Logs G c f:= ((tint G _).toContinuousLinearMap.comp (pushF B)).prod ((tint G _).toContinuousLinearMap.comp ((stamp B G).comp (pushG B)))
noncomputable def pushChart (G:Gauge) (i:S.Choices) : Positions (Joint B G) → ℝ:= Costree S G i ∘ relayB B G
variable (h:S.patch.Branches S.kernel G) (hm:Premier (main f p R))(hp:Critical B p R ρ)(hq:ClassicalMatch B p q R T ρ)
local notation "ζ"=> lyricP B ρ
local notation "M"=> center B ρ
include hm h hp hq
lemma steady (x:Positions (Primary c G))(y:Positions (Key B G)): let v:=center B ρ x+y; let z:=meetVar x v
    height f p R (stamp B G v)+Tensor.diagonal (Tensor.coeff (pushChart B G i) 2 0) z = height c q T x+(dotProduct y (Push.Uniform.block (priced B i p R) 0 *ᵥ y))/2:=by
    intro v z; have hv:=legP B i p R h hm; let w:= (∆ ζ 0) x; let X':=meetVar x (w+y)
    have he: rim C₀ X' X'= rim P (W X') (W X'):= hv.carriage (paint B G).toContinuousLinearMap X' X'
    rw [hessianP B i p R h hm] at he
    have ht:relayB B G z=((paint B G X').1,Bid.stretch B (paint B G X')):=by
        obtain ⟨he,hA⟩:= shiftScale B x (w+y); rw [show (W X').1= (tint G _) x from he,show Bid.stretch B (W X')= _ from hA]
        change (Ψ _ x, Ψ _ (stamp _ _ v))= _; rw [show v=w+y+imageCopy B G x from (by unfold v center; rw [_root_.add_apply,add_right_comm])]
    rw [← ht] at he
    let L:= relayB B G; have hc:=bornCosts i h; have hx:(flat S i p R)= (main f p R ∘ (ContinuousLinearMap.snd ℝ V (fieldDir G f 1)))+Costree S G i:=rfl; rw [hx, Premier.joined (hm.line (ContinuousLinearMap.snd ℝ V (fieldDir G f 1))) hc (relayB B G z)] at he -- exact comp issue?
    have hh: rim (main f p R ∘ (ContinuousLinearMap.snd ℝ V (fieldDir G f 1))) (relayB B G z) (relayB B G z)=rim (main f p R) (Ψ _ (stamp B G v)) (Ψ _ (stamp B G v)):= hm.carriage (ContinuousLinearMap.snd ℝ V (fieldDir G f 1)) _ _ -- specify
    rw [hh,← hc.carriage (relayB B G) z z] at he
    let A:= rim (main c q T) (Ψ _ x) (Ψ _ x); let Q:=dotProduct y (K*ᵥ y)
    have hM : rim C₀ X' X'= A+Q:= by
         have hx : rim C₀ X' X'= rim C₀ (meetVar x w) (meetVar x w)+Q:= pulse2 (paysCore B i p R h hm).1 (veil B R p ρ h hm hp) (tone B R p ρ h hm hp) (rose B i R p ρ h hm hp) x y
         rw [hx,show rim C₀ (meetVar x w) (meetVar x w)= A from posts B i R T p q ρ h hm hp hq x]
    unfold height; rw [Premier.second hm, Premier.second (show Premier (pushChart B G i) from hc.line L), Premier.second (pierce B i R T p q ρ h hm hp hq)]; rw [← mul_add]
    unfold pushChart; rw [←he,hM]; change 1/2*(A+Q)=1/2*A+Q/2; ring
end YM.MSbar.Rolling
