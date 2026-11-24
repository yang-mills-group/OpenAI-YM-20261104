import YM.RG16.Unmasked.Purchased
import YM.Integration.WilsonOriginalTwoFlatCapture

/-! The actual embedded site geometry of a separated physical grid. The
physical chamber and the period reduction are independent of the upper mesh
ratio. Each raw field is evaluated at its own original site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatGrid
open Function Filter Set Lattice RG Wilson Next.Rank Source OPE MergeProof
open Ribbons Accent Cells Extra.Histories RG16 RG16.Literal
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){I:Type}

theorem locations {c j:ℕ}(cj:c+1≤j)(o:I → Cover)
    (insideRoot:∀i,8*‖C.S.gridPoint j (o i)‖≤C.S.a (c+1))
    (apart:Pairwise fun i i'=>2*C.S.a j*(((C.path.levels.budget j).B:ℝ)^2) ≤
      ‖C.S.gridPoint j (o i)-C.S.gridPoint j (o i')‖) (p:ℕ):
    (∀i,C.S.place (snap C j p o i)=C.S.gridPoint j (o i)) ∧
    (∀i,loops C j p (snap C j p o i) (c+1)=0) ∧
    Edition.Spaced (C.path.levels.budget j).B (snap C j p o):=by
  have hs(i:I):‖C.S.gridPoint j (o i)‖≤1/8:=by
    have one: C.S.a (c+1)≤1:=(C.S.strictAnti.antitone (Nat.zero_le _)).trans_eq C.S.a_zero
    linarith only [insideRoot i,one]
  have exactSite(i:I):C.S.place (snap C j p o i)=C.S.gridPoint j (o i):=
    inside C j p ((hs i).trans (by norm_num))
  refine ⟨exactSite,fun i=>?_,fun i i' h=>?_⟩
  · apply Frontier6.Road.loops_zero C p j (c+1) (snap C j p o i) cj
    rw [exactSite];linarith only [insideRoot i,norm_nonneg (C.S.gridPoint j (o i))]
  · have cost:=(normC C j p (wrap (C.side j p) (o i-o i'))).2
    have compact:‖C.S.gridPoint j (o i-o i')‖≤1:=by
      rw [Frontier6.Road.grid_sub C j]
      exact (norm_sub_le ..).trans ((add_le_add (hs i) (hs i')).trans (by norm_num))
    rw [inside C j p compact,Frontier6.Road.grid_sub C j,map_sub] at cost
    simp only [separation,sub_zero] at cost
    exact_mod_cast (le_of_mul_le_mul_left ((apart h).trans cost)
      (mul_pos zero_lt_two (C.S.a_pos _)):
      (((C.path.levels.budget j).B:ℝ)^2) ≤ (separation (snap C j p o i) (snap C j p o i'):ℝ))

variable [Finite I] (d:I→ℕ)

/-- A fixed chamber works simultaneously for every literal addressed field and
for every unit counterterm, on all late cutoffs and every physical period. -/
theorem chamber (h:C.Makes)(J:ℕ):∀ᶠ N:ℕ in atTop,∀p c j:ℕ,∀hn:j≤N,∀hc:J≤c+1,∀cj:c+1≤j,
    ∀(o:I → Cover),(∀i,8*‖C.S.gridPoint j (o i)‖≤C.S.a (c+1)) →
    (∀(i:I)(v:C.label (d i)), Interior ((center C.S p ((hc.trans cj).trans hn) 0).chamber 0)
      (C.O N p v ((C.S.toDepth hn p).embed (snap C j p o i)))) ∧
    ∀v:C.label 0,Interior ((center C.S p ((hc.trans cj).trans hn) 0).chamber 0) (C.O N p v 0):=by
  filter_upwards [near_center C J 0 h,eventually_all.mpr (fun i:I=>near_center C J (d i) h)] with N unit arm
  intro p c j hn hc cj o house
  refine ⟨fun i v=>?_,fun v=>unit _ p 0 (by rw [latzero];simp [(C.S.a_pos _).le]) v⟩
  apply arm i _ p _ _ v
  rw [C.S.embeds_place]
  have small(i:I):‖C.S.gridPoint j (o i)‖≤1:=by
    have one: C.S.a (c+1)≤1:=(C.S.strictAnti.antitone (Nat.zero_le _)).trans_eq C.S.a_zero
    linarith only [house i,one]
  rw [RG16.Literal.snap,inside C j p (small i)]
  exact (house i).trans (C.S.strictAnti.antitone hc)

end YM.Integration.WilsonOriginalTwoFlatGrid
end
