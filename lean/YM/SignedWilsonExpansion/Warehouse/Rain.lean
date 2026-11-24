import YM.SignedWilsonExpansion.Warehouse.Election
import YM.SignedWilsonExpansion.Warehouse.Wish
set_option autoImplicit false
noncomputable section
namespace YM.Integration.Election.PaidP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extraction Lattice
open WilsonPhysicalWeakWallStaff.ReStaff
universe u
variable {G:Gauge}{R:Run G}{h:G.Simple}{a:Axis}{ε:ℝ}{s:OrderS G}{T:Campaign R}{W:Campaign.Pillars R T}

lemma puddle (p:PaidP.{u} a h ε s R T W) (f:Extraction.Order) : ∃M:PRAY R h, ∃ (g:Extraction.Order), M.f=f.refine g ∧ Nonempty {X:Climb.Scaling M.S// Pert.FirstExtension M.last X} := by
 obtain ⟨g, B, S, F, X, L, P, tune, trackP, trackU, first, stage, stress, pillar, proofP, _⟩:= p.way.refine f
 obtain ⟨H,Z,Y,bliss,_⟩:= stress.stress
 obtain ⟨day, d₁, d₂⟩:= mile h F H bliss trackP trackU p.paid.panels
 exact ⟨⟨f.refine g,S,F,trackU,trackP,pillar,H,Y,Z,bliss,day,d₁,d₂,L,P,stage,proofP⟩,g,rfl,⟨ X,first ⟩ ⟩
end YM.Integration.Election.PaidP
