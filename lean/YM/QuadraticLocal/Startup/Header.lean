import YM.QuadraticLocal.Startup.Arbor
import YM.QuadraticLocal.Startup.Warm
import YM.AllOrder.Quay.Native
/-!
# Expose the actual top unmarked Assembly.Wait (width)

 DAY before calling Mark. Extends existing Quay supplies preparations
 to also reclose new packed masks at +1 support inside THIS Pillar. No changing
 the vacuum labels according to the query. Aiming arbitrary additive log shifts.
 No strengthening along tape except what Startup.Mark needs for its path.Frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
-- fiscal.ingredients
variable (k)
open Progress.DirectedRecipe Rosary.Devotion
local notation "B"=>p.B
local notation "sM"=> offerS G p (tile h G) (Age.scope (k+2)) (gStep β)
local notation "sH"=> pulpit h β G k
local notation "w"=>Start.weight h β
local notation "t"=> p.threshold
local notation "I"=> Key n
local notation "Q"=> dictionary G n
local notation "J"=> Quay.rush (G:=G) (n:=n) p h β
variable (x:Site n)(U:Config G n)
-- fare. std. Hard THE SAME but no other bindings
local notation "V!"=> drum (G:=G) (n:=n) p h β
local notation "M"=> Pipes.pours Q V!
local notation "L"=>raw G n h p β
variable {σ l w' κ C d γ:ℝ}
-- variable names conflicts from HEADQ?
section
variable (hp:Start.Loan p l σ κ γ) (hc: WilsonStartup.Decent h p)(he:l≤β)
variable (hz : p.threshold≤Start.threshold G p.order p.power) (h0:p.threshold≤ permit G k p.order p.power)(hb:4*(k+4)≤p.B) (hβ:0<β)
    (hM:∀ i:Site n,Till.Fairness p i (court i p.B) (offerS G p (Crest.tile h G) (Age.scope (k+2)) (gStep β) n i) C)
-- nomenclature.PowerE. starts.
local notation "U"=> Real.exp -- conflicts U above, change
local notation "σ'"=> costFace (|w| *perCost p k G)
local notation "a"=> U p.supportExponent*C
local notation "a₀"=> U p.supportExponent*σ'
local notation "b"=> wad p (|w| *item G p)
local notation "c₀"=>coupon κ γ
local notation "T"=> Extra.Iteration.numbering (Key n⊕ℕ)
local notation "S✧"=> Burn.keys n
local notation "V₁"=> Herb.pumps (basil p sH) S✧ (Cane.haul J T Q)
local notation "W₁"=> Herb.fluid (basil p sH) S✧ (Cane.sap J T V!)
local notation "V₂"=> Herb.pumps (basil p sM) S✧ V₁
local notation "W₂"=> Herb.fluid (basil p sM) S✧ W₁
local notation "F"=> Design.top G h
include hp hc he hz h0 hb hβ hM
lemma served (ρ:ℝ)(H: Payments.Rates p.B w' (coupon κ γ) (wad p (|w| *item G p)+QuadraticLocal.Willow.haloSlack p.B) ρ):∃ (X:Pipes G n)(v:Tap G n), let Y:= finish (F) h p X v β 0; Ingredients X v p (a+a₀) w'∧ Y.eval=Wilson.bare β ∧ QuadraticLocal.Hard.Install Y.activities p w' (QuadraticLocal.Willow.haloSlack p.B)∧∃ T': Seed Y (sM), Candor p Y.activities (Set.range T'.model) a a₀:= by
 let hx:= currency (G:=G) (n:=n) p h β hp hc he; let hy:= todays (n:=n) p h β hc.radius hz; have hG:= Cane.out hx hy (T) (1:Config G n); rw [add_zero] at hG; have hL:= (altar (n:=n) k p h β · h0 hc.radius); let hℓ:= note_roam k h β n (G:=G); have hV:=plant («M»:=sH) hG hL hℓ|>.1; rw [add_zero] at hV; obtain ⟨hC,hC',hR⟩:= plant («M»:=sM) hV hM (Tilt.signed _ _ _ _ n); have hp':= (hC.relax le_rfl le_rfl (le_add_of_nonneg_right (QuadraticLocal.Willow.spare_pos _|>.le))).digest H
 refine ⟨V₂,W₂,hp',funext fun U'=>?_, ?_, ?_⟩
 · have hT:(Pipes.pours V₂ W₂).additive p U'=(raw G n h p β).additive p U'+ ∑' i:ℕ,(W₂).logarithm i U':= by
       rw [turn hV hM (Tilt.signed _ _ _ _ n)]; -- unfolds.mask
       have hz:=turn («M»:=sH) hG hL hℓ U'; have he' :(Pipes.pours V₁ W₁).additive p U'=∑ x:Site n,masked t (court x p.B) (sH n x) U':= hz.trans (by change _+(M).additive p U'=_; rw [nothing p h β U' hp hc he,add_zero]); rw [he',add_comm (Finset.sum ..) (Finset.sum ..), ← Finset.sum_add_distrib]
       have hw' := Cane.mellow hx hy (T) U'; have hζ :(∑' i:ℕ,(V!).logarithm i U')=0:=tsum_zero;
       rw [hζ,add_zero] at hw'; exact (site_voice k p h β U' hb hβ).trans (congr_arg _ hw'.symm)
   rw [hp'.unshifted, ← Start.evaluates hc, Rep.eval,Rep.eval]; dsimp only [Progress.DirectedRecipe.trunk,Bid.Cake,Rep.exponent]; rw [hT]; change U (0 * _ - _ -_) * (L).gas p U' * _= U (0 * _ -_ - (L).additive p U') * (L).gas p U'; rw [mul_right_comm _ ((L).gas ..),← Real.exp_add]; congr 2; ring
 · obtain ⟨ht,he',u,v,hT,hy,hZ⟩:= hC
   let I' := Pipes.pours V₂ W₂
   let hf:= ht.support; let he : I'.ForcedFamily p:= hf; refine ⟨I',c₀,⟨(V₂),W₂,rfl,rfl,rfl,rfl,b,ρ, ?_, ?_, H⟩, he.sym, he.meas, he.permit, he.reads,u,hy.1,(fun i U'=> (hT i U').1),hy.2⟩
   · exact ⟨ht.steady,ht.looks,ht.reads,ht.visits⟩
   refine ⟨v,hZ.1,fun i U'=> (hT i U').2,hZ.2⟩
 let T0:Seed (trunk F h p V₂ W₂ β 0) (sM):= seed (trunk F h p V₁ W₁ β 0) _ (Tilt.regional _ _ _ _); obtain ⟨T',heT⟩:= Fusion.sharp sM β 0 T0; refine ⟨T',?_⟩; rw [heT,show T0.model = pivot n from rfl]; exact Set.range_comp (Rack.upE V₂) (pivot n) ▸ Fusion.paid _ hp' F h hR
end
end YM.AllOrder.Quay
