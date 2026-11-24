import YM.TraceExtension.Prom.Front.West.Equity

/-! All original ordinary faces have the same deposited Wilson field at
each matrix argument and the same inherited finite chamber data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickSpun
open RG Lattice Wilson Cells Marker
open Next.Rank Next.Rank.Atlas Next.Rank.Tapes Next.Rank.Tapes.West
open Next.Rank.Ribbon Next.Rank.Station Next.Rank.Rise Next.Rank.Normal Next.Rank.Spindle Glyph Exponential Function
open scoped BigOperators Classical
variable {G:Gauge}{C:Family G}{k l N p n θ:ℕ}{Ψ:AtlasData G C.S p}{P:Rep G (C.side k p)}
    {d:Fin n→ℕ}{q:ℕ}
theorem original (F:(i:Fin n)→StampDuty C k N p (d i) θ P q Ψ)
    (v:(i:Fin n)→C.label (d i))(s:Fin n → Cover)(h:l≤k)(y:Chamber G C.S l p→ℝ)
    (inv:invariantAt (C:=C) k (wood C.path.levels k) p Ψ):
    spunW (track Ψ) (fun i=>prefaced (F i) (v i) (s i)) h y=
      Answer Ψ s h (fun i=>(F i).heater (v i)) (fun U=>(y U:ℂ)):=by
  ext i
  apply Eq.symm
  change _=text y (shelve (track Ψ) h (∏j∈i.val,prefaced (F j) (v j) (s j)))
  rw [forecast]
  simp_rw [genesis _ _ inv]
  rfl

end YM.Integration.WilsonPhysicalThermalWickSpun
end
