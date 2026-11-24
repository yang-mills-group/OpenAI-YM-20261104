import YM.Integration.WilsonPhysicalThermalWickMeridian
import YM.Integration.WilsonPhysicalThermalWickPrice

/-! The original Schur word has two named placements. The between-site
Maxwell kernel is left unchanged by reciprocal changes of the two raw slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickReturned
open Lattice Wilson RG Labels Finset MvPolynomial Function
open Next.Rank Next.Rank.Normal Next.Rank.Prayer Next.Rank.Configuration Next.Rank.Beamer Next.Rank.Common
open WilsonPhysicalThermalWickRescale
open scoped BigOperators Classical
variable {G:Gauge}{n d M:ℕ}{V:Type*}

theorem within {x:Points n}(hx:x∈conf n)(i j:Fin n × KeyIn G d)(same:i.1=j.1):
    (currentX hx G d).cov i j=0:=by
  have location (u:Fin n × KeyIn G d)(t:Fin n × Maxwell.Slot G)
      (h:t∈(perSlot (fun _:Fin n=>mapper (d:=d) (G:=G)) u).support):t.1=u.1:=by
    obtain ⟨a,_,e⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support h)
    exact (congrArg Prod.fst e).symm
  unfold currentX scope treats
  simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro v hv
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro u hu
  simp [frameX,(location i u hu).trans (same.trans (location j v hv).symm)]

theorem original {x:Points 2}(hx:x∈conf 2){T P E B e r A:ℝ}(scale:1≤A)
    (Y:Meridian (G:=G) d hx T P E B e r M)(f:V→Address G)(roof:∀i,street (f i).1≤M)
    (Γ:Fin 2→Fin 2→Bridge G)(μ:Fin 2→Horizon G)(symm:∀i j u v,Γ i j u v=Γ j i v u)
    (earned:Reads (G:=G) d hx r Γ μ M P E)(p:Fin 2→poly (KeyIn G d))(q:Fin 2→ℕ)
    (h:∀i,pure (q i) (p i))(S:Finset (Fin 2))(D:ℕ)(degree:(pot S p).totalDegree≤D):
    let Q:=primary d f r Γ symm
    let m:=seen d f r μ
    let error:=A^2*max (E*T) (E*T*T)
    ‖∏i∈S,(WilsonPhysicalThermalWickPrice.scales A i)^(q i)‖*
        ‖blend (Particle.ferry Q) (m∘Particle.polar) (pot S p)-blend (currentX hx G d) 0 (pot S p)‖≤
      Rise.coin (pot S p)*(error*priced (B+error) D):=by
  exact WilsonPhysicalThermalWickPrice.original scale _ _ _ (within hx)
    (WilsonPhysicalThermalWickMeridian.original hx Y f roof Γ μ symm earned).2 p q h S D degree

end YM.Integration.WilsonPhysicalThermalWickReturned
end
