import YM.RG11Proof.Fields.Conn

/-! Allow the first order slope premise to be computed as a connected response
against the diagnostic. Still need prove that independent prescription's value
and agreement of leading covariances, not paid by framing estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.Pert YM.RG11.Jets Function Set Labels Maxwell Position Extra.FD PertExtension.Position
open Triangle
open scoped Classical BigOperators
variable {G:Gauge} {F:Frames G}(hg:G.Simple) {d:ℕ}(h:6≤d) (B:Basis F d)

-- Three-slot through-first-order readout. `large` refers exactly to our
-- b,U,U lifted fields; `small` reads the other two after q_perm to put missing
-- input at zero before deletion; `solo` this missing input. Pass from the
-- *same* normalized measure/independent series prescription before invoking.
def withConnected (D:ArrayAt B.J ℝ form) (hD:∀ v,constantCoeff (D v)=rowZero B v)
   (T₀ : (freeTable F).Basic) (T:Test 3→MultilinearMap ℂ (fun _:Fin 3=>E F d) ℂ)
   (hT : ∀ w,tangent (D (Fields.take h B w))=(T (Fields.take h B w).1.test (fun i=>B.b (w i))).re)
   (hξ : ∀ z v,T (z • profileChoice) v=z * T profileChoice v)
   (large:Points 3→ℂ⟦X⟧) (small solo:Points 3→Fin 3→ℂ⟦X⟧) (vacuole:Points 3→Fin 3→Points 1)
   (ho:T profileChoice (Fields.triple h F)=profileChoice.applyTo (fun x=>coeff 1 (large x)))
   (hs : ∀ x∈conf 3,∀ i,constantCoeff (solo x i)=visible F d (vacuole x i) (fun _=> Fields.triple h F i))
   (hp : ∀ x∈conf 3,∀ i,constantCoeff (small x i)=visible F d (dropX x i) (dropLabels (Fields.triple h F) i))
   (hr : profileChoice.applyTo (fun x=> coeff 1 (Fields.conn large small solo x))= cTest G):RulerTest B.guard D:=
  probeRuler F hg h B D hD T hT hξ
    (ho.trans ((Test.apply_eq _ (agree hg h T₀ _ _ _ _ hs hp |>.symm)).trans hr))
end YM.RG11.Fields
