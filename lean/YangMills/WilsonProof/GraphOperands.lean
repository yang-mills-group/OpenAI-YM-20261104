import YM.Euclid.Differential
import YangMills.PerturbativeMatching.GraphCoefficients
import YM.XSpace.Influence

set_option autoImplicit false
noncomputable section

namespace YM.XSpace.Normalize
open Maxwell.Free
variable {G : Gauge} {j d : ℕ}
abbrev up (h:j≤d): Sec G j→ₗ[ℂ] Sec G d:= Submodule.inclusion (chain h)
end YM.XSpace.Normalize

namespace YM.XSpace.Structure1
open XSpace.Normalize
abbrev Point (G:Gauge) (d n:ℕ):= MultilinearMap ℂ (fun _ : Fin n=> Sec G d) ℂ
end YM.XSpace.Structure1

namespace YM.FVA2.Arrival.Schedule
open MS MS.Tone
variable {n : ℕ}
def plot (x:Points n) : Fin n→ QP := fun i=> Theater.out (x i)
end YM.FVA2.Arrival.Schedule

namespace YM.FVA2.Teller
def logNu (μ:ℝ):ℝ:= Real.log μ + (Real.eulerMascheroniConstant - Real.log (4*Real.pi))/2
end YM.FVA2.Teller

namespace YM.FVA2.Dframe
open MS MS.Local.Physical MS.Menus MS.Land XSpace.Structure1
variable {G : Gauge} {B : Deck G} {n d : ℕ}
abbrev Toon (G:Gauge)(d:ℕ):= Glyph (Press.portDeck G) d
abbrev panel (i: Glyph B d): Plaid B i.size:= ⟨i.2.1,i.2.2 ⟩
abbrev flash (i:Glyph B d): MS.Rake.Label B:= ⟨ _, panel i ⟩
local notation "Π" => Press.portDeck G
local notation "W" => Fin n
def each (t:Fin n→Toon G d) : Point G d n:= (MultilinearMap.mkPiAlgebra ℂ W ℂ).compLinearMap (fun i=> (Theater.Daylight Π d).coord (t i))
end YM.FVA2.Dframe
