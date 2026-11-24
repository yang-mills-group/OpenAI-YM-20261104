import YM.Next.RANK.Prayer

/-! Keep the epsilon bought on the original covariance and mean at the two
sites. The loss of one and two interpolation factors is paid only once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickMeridian
open Lattice Wilson RG Labels
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank
open scoped Classical
variable {G:Gauge}{V:Type*}{n d M:ℕ}{x:Points n}(hx:x∈conf n)
  {T P E B e r:ℝ}

theorem precision (Y:Meridian (G:=G) d hx T P E B e r M):
    Meridian (G:=G) d hx T P E B (max (E*T) (E*T*T)) r M:=
  {Y with precise:=le_max_left .., precision:=le_max_right ..}

theorem original (Y:Meridian (G:=G) d hx T P E B e r M)(f:V → Address G)
    (roof:∀i,street (f i).1≤M)(Γ:Fin n→Fin n→Bridge G)(μ:Fin n→Horizon G)
    (symm:∀i j u v,Γ i j u v=Γ j i v u)(earned:Reads (G:=G) d hx r Γ μ M P E):
    let Q:=primary d f r Γ symm
    let m:=seen d f r μ
    Sorts Q m B ∧ Nearby (Particle.ferry Q) (currentX hx G d) (m ∘ Particle.polar) 0 B (max (E*T) (E*T*T)):=
  Prayer.resolution d hx r _ (precision hx Y) f roof Γ μ symm earned

end YM.Integration.WilsonPhysicalThermalWickMeridian
end
