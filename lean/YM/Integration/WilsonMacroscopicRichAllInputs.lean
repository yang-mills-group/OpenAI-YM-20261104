import YM.Integration.WilsonMacroscopicRichDistantPoint
import YM.Next.UV_STRESS.Vary

/-! One price before both physical lengths, all positions and every source vector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichAllInputs
open Function Set Filter Finset YM YM.Table YM.Climb YM.PhysMS YM.Trace.Pilot YM.Next.UVStress
open WilsonMacroscopicRichReflectedRoster WilsonMacroscopicRichMovingPlane
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{n:ℕ}

def dates (n:ℕ)(r τ:ℝ):Fin (n+1)→ℝ:=Fin.append (fun _:Fin n=>r) (fun _:Fin 1=>τ)

def value (J:ℝ→tower S)(d:Caps (n+1))(r τ:ℝ)(x:Points n)(y:Points 1):
    MultilinearMap ℂ (fun i=>(Bel C.book).Field (d i)) ℂ:=
  (S.classMoment S d (placed r τ x y)).compLinearMap (fun i=>(J (dates n r τ i) (d i)).toLinearMap)

private theorem agree (J:ℝ→tower S)(d:Caps (n+1))(u:∀ i,(Bel C.book).Field (d i))(r τ:ℝ)(x:Points n)(y:Points 1):
    let j:Fin (n+1)→(Bel C.book).Tag:=fun i=>⟨d i,u i⟩
    value J d r τ x y u=S.useAt S (placed r τ x y) (Fin.append (fun i=>physical J r (j (Fin.castAdd 1 i))) (fun _:Fin 1=>physical J τ (j (Fin.natAdd n 0)) )):=by
  let j:Fin (n+1)→(Bel C.book).Tag:=fun i=>⟨d i,u i⟩
  have equal: (fun i=>physical J (dates n r τ i) (j i))= Fin.append (fun i=>physical J r (j (Fin.castAdd 1 i))) (fun _:Fin 1=>physical J τ (j (Fin.natAdd n 0))) := by
    funext i;refine Fin.addCases (fun a=> ?_) (fun a=> ?_) i
    · simp [dates,Fin.append_left]
    · rw [Subsingleton.elim a 0];simp [dates,Fin.append_right]
  change S.useAt S _ (fun i=>physical J (dates n r τ i) (j i)) = _
  rw [equal]

theorem original (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J)(d:Caps (n+1)) (K:Set (Points n))(L:Set (Points 1))
    (compact:IsCompact K)(far:IsCompact L)(safe:K⊆conf n)(nz:∀y∈L,y 0≠0):
    ∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η →∀x∈K,∀y∈L,∀u:∀i,(Bel C.book).Field (d i),
      ‖value J d r τ x y u‖≤ B*∏i,‖u i‖:=by
  let V (i:Fin (n+1)):=(Bel C.book).Field (d i)
  have fixed (a:Code V):∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η →∀x∈K,∀y∈L,‖value J d r τ x y (combination V a)‖≤B:=by
    let v(i:Fin (n+1)):(Bel C.book).Tag:=⟨d i,combination V a i⟩
    obtain ⟨η,ep,B,bp,U,hu,bill⟩:=WilsonMacroscopicRichDistantPoint.original F J H K L compact far safe nz (fun i=>v (Fin.castAdd 1 i)) (v (Fin.natAdd n 0))
    refine ⟨η,ep,B,bp,U,hu,?_⟩;intro r hr τ hτ ratio x hx y hy;rw [agree]
    exact bill r hr τ hτ ratio x hx y hy
  choose η pos M positive U region bill using fixed
  have common:∀ᶠ s in trail,∀a:Code V,s≤η a:=Filter.eventually_all.2 fun a=>eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (pos a))
  obtain ⟨s,hs,low⟩:= (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ s in trail,0<s) common).exists
  let Z(a:Code V)(i:Fin (n+1)):=LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (V i)).coord (a i))
  let size(a:Code V):=∏i,‖Z a i‖
  have sn(a:Code V):0 ≤ size a:=prod_nonneg fun i _=>norm_nonneg (Z a i)
  let B:=∑ a:Code V,size a*M a
  refine ⟨s,hs,B,sum_nonneg fun a _=>mul_nonneg (sn a) (positive a),{r|∀a:Code V,r∈U a},Filter.eventually_all.2 region,?_⟩
  intro r hr τ hτ ratio x hx y hy u
  have price(a:Code V):‖coords V a u‖ ≤ size a*∏i,‖u i‖:=by
    unfold coords size;rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(Z a i).le_opNorm _)
  rw [basis_tuple V u (value J d r τ x y)]
  calc _ ≤ ∑ a:Code V,‖coords V a u * value J d r τ x y (combination V a)‖:=norm_sum_le _ _
       _ ≤ ∑ a:Code V,(size a*M a)*(∏i,‖u i‖):=sum_le_sum fun a _=>by
            rw [norm_mul];exact (mul_le_mul (price a) (bill a r (hr a) τ (hτ a) (ratio.trans (low a)) x hx y hy) (norm_nonneg _) (mul_nonneg (sn a) (prod_nonneg fun i _=>norm_nonneg _))).trans_eq (by ring)
       _ = B*∏i,‖u i‖:=(sum_mul ..).symm
end YM.Integration.WilsonMacroscopicRichAllInputs
