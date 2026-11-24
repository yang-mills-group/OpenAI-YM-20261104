import YM.GradedFar.Coat
/-!
# G6 expanses: pull all arguments grade by grade
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (P:ℝ→tower S)
    {A B:Type*} {α:Filter A} {U:A→B→Prop} {L W r s:A→B→ℝ} {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}
local notation "Cst" => Cast F R

abbrev WholeInput (G:Gauge) (d:I→ℕ) := (i:I)→Sec G (d i)
def moved (r:ℝ) (u:WholeInput G d) : Labels S d := fun i=> assign P r (d i) (u i)
def low (u:∀ i,Cst (d i)) (i:I) := Cast.cost F R (u i)
def stars (u:∀ i,Cst (d i)) : Labels S d:= fun i=> Cast.push F R (u i)
def actors (u:∀ i,Cst (d i)) : Labels S (low (d:=d) F R u):=fun i=>R.actor _ (u i).2

def coal (p:∀ i,Cst (d i))(r:ℝ)(u:WholeInput G d) := ∏ i, coatRead F R P r (p i) (u i)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
lemma costing (Φ : MultilinearMap ℂ (fun i=> S.Field (d i)) E) (r:ℝ)(u:WholeInput G d) :
    Φ (moved P r u)=∑ i, coal F R P i r u • Φ (stars F R i) := by
  have h: moved P r u = fun i=>∑ j:Cast F R (d i), coatRead F R P r j (u i) • Cast.push F R j :=
      funext fun i=> (Cast.produce F R _).symm
  rw [h,Φ.map_sum]; exact Finset.sum_congr rfl (fun i _=> Φ.map_smul_univ ..)

lemma earnsCoal (H:Bedroom α U L r) {u:A→B→WholeInput G d} (p:∀ i,Cst (d i)) (Hw:∀ i,Coat F R P (d i))
    (hu:∀ᶠ a in α,∀ z i, U a z → width (u a z i) ≤ 1): Sold α U L
    (fun a z=> r a z^(∑i,low (d:=d) F R p i)) (fun a z=> coal F R P p (r a z) (u a z)):=by
  have h : ∀ s:Finset I, Sold α U L (fun a z=> r a z^(∑i∈s,low F R p i))
      (fun a z=>∏ i∈s, coatRead F R P (r a z) (p i) (u a z i)):=by
    intro s; induction s using Finset.induction_on with
    | empty=> simpa only [Finset.sum_empty,Finset.prod_empty,pow_zero] using Sold.closed (φ:=α) (B:=U) (L:=L) (1:ℂ)
    | @insert i q hi ih=>
      have h₀ : Safe α U L (fun a z=>r a z^(∑i∈q,low F R p i)):= (H.logs.and H.pos).mono fun a h z he=>
        ⟨h.1 _ he, pow_nonneg (h.2 _ he|>.le) _⟩
      have h:= ih.mul h₀ (earnFrom F R P H (p i) (Hw i) (hu.mono fun _ h z hz=>h z i hz))
      simpa only [Finset.sum_insert hi,Finset.prod_insert hi,pow_add,low] using h
  exact h Finset.univ

lemma present (H:Bedroom α U L r) {Φ:A→B→MultilinearMap ℂ (fun i=> S.Field (d i)) E} {u:A→B→WholeInput G d}
    (Hw:∀ i,Coat F R P (d i))(hu:∀ᶠ a in α,∀ z i, U a z → width (u a z i) ≤ 1)(hw:Safe α U L W)
    (cost : ∀ p:∀ i,Cst (d i), Sold α U L (fun a z=> W a z / (r a z^(∑ i,low (d:=d) F R p i)))
        (fun a z=> Φ a z (stars F R p))): Sold α U L W (fun a z=> Φ a z (moved P (r a z) (u a z))) := by
  have hW(p:∀ i,Cst (d i)) := Sold.smul (f:=fun a z=>Φ a z (stars F R p)) (hw.joint
    ((H.pos.and hw).mono (fun a h z he=> div_nonneg (h.2 z he).2 (pow_nonneg (h.1 _ he |>.le) _))))
    (cost p) (earnsCoal F R P H p Hw hu)
  refine (Sold.sum (x:=Finset.univ) hw (fun i _=> (hW i).more (H.logs.mono fun a ha z he=> zero_le_one.trans (ha z he))
    (H.pos.mono fun a ha z hz=>le_of_eq ?_))).congr (fun a z=> (costing F R P (Φ a z) ..).symm)
  exact mul_div_cancel₀ _ (pow_pos (ha z hz) _).ne'

def delivery (w : Labels S e) : MultilinearMap ℂ (fun i=> S.Field (e i)) E →ₗ[ℂ] E := ⟨⟨fun f=>f w,fun _ _=>rfl⟩,fun _ _=>rfl⟩
lemma performance (H:Bedroom α U L r)(K:Bedroom α U L s)
    {Φ:A→B→MultilinearMap ℂ (fun i=> S.Field (d i)) (MultilinearMap ℂ (fun i=> S.Field (e i)) E)}
    {u:A→B→WholeInput G d}{v:A→B→WholeInput G e} (Hw:∀ i,Coat F R P (d i))(Hw':∀ i,Coat F R P (e i))
    (hu:∀ᶠ a in α,∀ z i, U a z → width (u a z i) ≤ 1)(hv:∀ᶠ a in α,∀ z i, U a z→ width (v a z i) ≤1)
    (hw:Safe α U L W)
    (cost : ∀ (p:∀ i,Cst (d i))(q:∀ i,Cst (e i)), Sold α U L
        (fun a z=> W a z / (r a z^(∑ i,low (d:=d) F R p i)*s a z^(∑ i,low (d:=e) F R q i)))
        (fun a z=> Φ a z (stars F R p) (stars F R q))):
    Sold α U L W (fun a z=> Φ a z (moved P (r a z) (u a z)) (moved P (s a z) (v a z))) := by
  apply present (Φ:=fun a z=>(delivery (e:=e) (E:=E) (moved P (s a z) (v a z))).compMultilinearMap (Φ a z)) F R P H Hw hu hw
  intro p; apply present (Φ:=fun a z=>Φ a z (stars F R p)) F R P K Hw' hv
    (hw.joint ((H.pos.and hw).mono fun a ha z hz=> div_nonneg (ha.2 z hz).2 (pow_nonneg (ha.1 _ hz |>.le) _)))
  intro q; simpa only [div_div] using cost p q

end YM.Integration.GradedFar.Fork
