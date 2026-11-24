import YM.GradedFar.Matrix
import YM.GradedFar.Vacant
/-!
# (M.4) detectors

Use the point option. Same bank applied to both moments; importantly our reflection Gram audit
**is at the farther length s**, not at the moving r of the output. That's why we need compact
prices/phase estimate (use G9 hypothesis on a noFar roster instead of composing them again from
QScale & G4). Also with this point option we use exactly the orientation in `Bank` on the
+time side, for using the project's `GramP` result (reflected-conjugate inserted). Sign of the Far
direction immaterial to (M.3); then fixed everywhere. Continuum prices uniform even over Center.

As in the proof pay the matrix costs again on converting between homes. These lean statements track
pointwise horizon geometry, not constructing a grid implementation of *payment for the inverse*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Finset Filter Function Set Spec Table Extraction
open OPE OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar FVA2.Scale FVA2.O.Score
open FVA2.Dframe MS MS.Book MS.Fleet MS.Land FVA2.Register
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
    (F: Final C fo S)(J:ℝ→tower S)
local notation "port" => RootG

variable (h:ℕ)
-- `h` used in the whole cost here, not replaced by Near estimator basis.
def Detect (ω:Viewers F) (o:E4)(r T:ℝ) : Sec G h →ₗ[ℂ] Sheet G h:=
    Bank.place h (today F J ω o r (r*T) (r*T) 0 port)
lemma detects (ω:Viewers F)(o:E4)(r T:ℝ)(u:Sec G h)(i: Toon G h):
    Detect F J h ω o r T u i = atCenter F J h ω o r T port (Bank.play i) u := rfl 

-- higher-power leading matrix term ready on the compact two-point geometry. This binds a grade statement,
-- then transport uses matrix margin on the **same** Sec horizon and station.
abbrev combo (_h:ℕ) (a b:Sec G _h): Inputs G (fun _:Fin (1+1)=>_h) := Fin.append (m:=1) (n:=1) (fun _=>a) (fun _=>b)
lemma towall (A:Arenas G)(u v:Sec G h)(t:ℝ): Bank.initial A h (fun _=>u) (fun _=>v) =
    crop 0 t (FormalCompact A h (fun _=> le_refl h) (⟨outgoing port,ok_wall⟩:Stage (1+1)) (combo h u v)):= by
  rw [Bank.initial,rawCoeff_apply _ _ _ _ _ _ _ ok_wall]; simp only [crop_eq,FormalCompact,PowerSeries.coeff_mk]
  simp; rfl
lemma bothWall (ω:Viewers F)(o:E4)(r:ℝ)(hr:0<r)(a b:Sec G h):
    today F J ω o r r r (d:=Output h) (e:=Output h) 0 port (fun _=>a) (fun _=>b)=
      TrueCompact F J ω r o (outgoing port) (combo h a b) := by
  rw [today_apply,TrueCompact, whole_observed, Orbits.observed]
  let e : Fin 1⊕ Fin 1 ≃ Fin (1+1):= finSumFinEquiv
  have hx: Injective (beside (sites o r (0:Points 1)) (sites o r port)):=by
    simpa only [mul_one, one_smul] using radius_conf (T:=1) hr o (by exact one_smul ℝ port |>.symm ▸ ok_wall)
  refine Fork.renameRead e (spectate F ω).laws.toSymmetric hx ?_ ?_
  · funext i; rcases i with i|i <;> fin_cases i <;> rfl
  funext i; rcases i with i|i <;> fin_cases i <;> rfl
lemma combo_box {a b:Sec G h}(hu:width a≤1)(hv:width b≤1): Box (combo h a b) 1:= by
  refine (boxes zero_le_one).2 fun i=>?_ ; fin_cases i
  · exact hu
  · exact hv

variable (N:WilsonPrescription G) {hG:G.Simple}(Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:MS.Land.Prescription (Press.portDeck G)}(H:Main.Match N hG Z σ true)(ν:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G

variable {Λ B:ℝ} (hΛ:0 < Λ)(hB:0<B) {t:ℝ→ℝ}
-- exact hypothesis taken: order-zero compact forecast (any clearance onset requested), suffices
-- for margin at decreasing s. also needs G1 for moving comparison of centers.
abbrev LeadingTicket (h:ℕ)(t:ℝ→ℝ) (N:WilsonPrescription G)(Λ B:ℝ):= RoundPoint F J t
    (Scale.Measure.outlook N.scheme N.criterion) (d:=fun _:Fin (1+1)=>h) (fun _=> le_refl h) (nofare h)
    Λ B 0 {outgoing port} {0}
variable (fund:LeadingTicket F J h t N Λ B) (predict:FrameForecast J t (GroupS.gaugeN N.scheme N.criterion Z ν) h Λ B)

include hΛ hB H ν fund in
lemma margin_bounds :∃ b:ℝ,1≤b ∧ ∀ᶠ s in trail,∀ ω o x,width x ≤
    b * ‖Bank.place h (today F J ω o s s s 0 port) x‖ := by
  have H' := (H.separatedOPE ν).wilson
  obtain ⟨b,hb,e,he,Ht⟩:=Bank.stable (h:=h) H'.wardRank
  obtain ⟨C,hC,H''⟩:=compact_price F J hG (K:={outgoing port}) (singleton_subset_iff.mpr ok_wall) t A 0 _ hΛ hB fund
  have hp : Tendsto (fun r => C*g r) trail (𝓝 0):= by simpa only [mul_zero] using (Coupling.conforms hG (strength_coupling hG)).const_mul C
  refine ⟨b,hb,?_⟩
  filter_upwards [self_mem_nhdsWithin, H'', hp.eventually_le_const he] with s (hs:0<s) hC hp ω o
  apply Ht
  intro a ha; apply (pi_norm_le_iff_of_nonneg he.le).2; intro i
  change ‖Bank.place _ _ _ i-Bank.place _ _ _ i‖ ≤ _; rw [Bank.placed,Bank.placed,norm_sub_rev]
  specialize hC ω o _ (Set.mem_singleton _) (combo h a (Bank.detector i)) (combo_box h ha (Bank.detector_width _))
  rw [← bothWall _ _ _ _ _ s hs,← towall,pow_one] at hC; exact hC.trans hp

lemma transformer (ω:Viewers F)(o:E4)(r T:ℝ):
    (Detect F J h ω o r T).comp (relative J r (r*T) h).toLinearMap= Bank.place h (today F J ω o (r*T) (r*T) (r*T) 0 port):= by
  ext1 a; funext i; rw [LinearMap.comp_apply, Detect, Bank.placed, Bank.placed, today_apply,today_apply]
  have he (r t:ℝ): sites o r (0:Points 1)=sites o t 0:= funext fun i=>by simp [sites]
  rw [he r (r*T)]; congr 1; funext i; exact atHome ..

include H hΛ hB predict fund
theorem Wall_inverse : ∃ b:ℝ,1 ≤ b ∧ ∀ᶠ r in trail, ∀ T:ℝ,
    1 ≤ T → T ≤ Λ*(g r)^(-B) → ∀ ω o, ∃ hP : Injective (Detect F J h ω o r T), Bank.invPrice _ hP ≤ b*T^h := by
  obtain ⟨b,hb,H'⟩:= predict.1; obtain ⟨b',hc,E⟩:= margin_bounds F J h N Z H ν hΛ hB fund
  refine ⟨b*b',one_le_mul_of_one_le_of_one_le hb hc,?_⟩; filter_upwards [H', out_radius hG (U:=Λ) (B:=B) _ E] with r hr he T hT hq ω o
  let V := Detect F J h ω o r T; let R := relative J r (r*T) h
  have hV:= transformer F J h ω o r T; have ht:0≤ b*T^h:=by positivity
  apply Bank.margin_inverse (by positivity)
  intro x; let y:= R.symm x; have hx:R y=x:=LinearEquiv.apply_symm_apply ..
  have hx' := he T hT hq ω o y; rw [← hV] at hx'; change width y≤ b'*‖V (R y)‖ at hx'; rw [hx] at hx'
  calc _ = width (R y):=by rw [hx]
       _ ≤ b*T^h * (b' * ‖V x‖):= (op_use R.toLinearMap y).trans (mul_le_mul (hr T hT hq) hx' (width_nn _) ht)
       _ = _:=by unfold V; ring
end YM.Integration.GradedFar
