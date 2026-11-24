import YM.Integration.WilsonOlderFreshLocatedSource
import YM.Integration.WilsonOlderFreshLocatedBook

/-! The exact two premise families used by LocatedFunded, on the true
located group words and all retained lags. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedPayment
open Filter MeasureTheory Lattice Wilson RG Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FormalBulk08 City Pose
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d D N per b j:ℕ}
local notation "axes" => Letter (R.family.labels.level d)
local notation "side" i:max => R.family.side i per

def Full (d:ℕ){D:ℕ}(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (digit:∀i,Site (R.family.S.block i))(N per beginAt Q q:ℕ)
    (Ψ:∀i,Rep G (R.family.side i per))(sites:∀i,Site (R.family.side i per))
    (book:(i:ℕ) → Letter (R.family.labels.level d)  →  Config G (R.family.side i per)  →  ℂ)(fare:ℝ):Prop:=
  let g:=fun i=>ConnectedActivityE6.Coat.gStep (R.family.path.rep N per i).beta
  (∀i,beginAt ≤ i → i ≤ N → ∀u,Integrable (fun U=>((Ψ i).eval U:ℂ)*book i u U) (prior G _)) ∧
  (∀i,beginAt ≤ i → i<N → ∀(t:Fin (Q+1))(w:Letter (R.family.labels.level d)),
     ∃z:store R.family d per i,Paid R (Ψ i) (sites i) z (fare*(g i)^q) ∧
       transition (C:=R.family) d N per i (film (Ψ (i+1)).eval (book (i+1) w) (g i) t.val)=
         film (Ψ i).eval (nextWord R wood a depth digit N i Q (g i) (book i) t w) (g i) t.val+
           z.density (sites i) (R.family.localSection d) (Ψ i))

def fare (ε:ℝ)(q:ℕ)(f:ℝ):ℝ:=5*ε*3^q*(1+f)

theorem reserve {x y ε F₁ F₀:ℝ}(xp:0 ≤ x)(yp:0 ≤ y)(ep:0<ε)(f0:0 ≤ F₁)(step:x ≤ 3*y)(ratio:F₁ ≤ F₀)(q:ℕ):
    5*ε*x^q*(1+F₁) ≤ fare ε q F₀*y^q:=by
  calc
    _  ≤  5*ε*((3*y)^q)*(1+F₀):=mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ xp step q) (by positivity))
      (by linarith) (by linarith) (by positivity)
    _ = _:=by rw [mul_pow];unfold fare;ring

theorem enlarge {Ψ:Rep G (side j)}{site:Site (side j)}{z:store R.family d per j}{u v:ℝ}
    (paid:Paid R Ψ site z u)(cost:u ≤ v):Paid R Ψ site z v:=
  ⟨paid.1,rem_mono paid.2.1 cost,paid.2.2.trans cost⟩

end YM.Integration.WilsonOlderFreshLocatedPayment
end
