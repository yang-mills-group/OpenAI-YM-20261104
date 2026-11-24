import YM.Integration.WilsonOlderFreshGraphArmada

/-! One approved numerical price pays all the independently grounded atoms
on their actual root. The physical support and rent are identical at every
test amplitude. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphWallet
open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open scoped Classical BigOperators Topology
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
variable {G:Gauge}{n:Side}{Q d:ℕ}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit) (C:Fin (Q+1)→ℝ) (σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest) (d0:0<d)
variable (A:Unit→Set ℂ)
local notation "M"=>material S W C σ paid legal d0 (value A)
theorem at_price (σ0:0≤σ) (cap:∀t,‖value A t‖≤1)
    (w b:ℝ) (gain:0<w) (b0:0<b) (budget:w*gross S C σ≤b)
    {ord seats shelf:ℕ}(qo:Q ≤ ord)(seats1:1 ≤ seats)(ds:d ≤ shelf):
    Scene.Armada M (fun _=>w) (fun _=>d) σ b ord seats shelf:=by
  have one:(w/b)*gross S C σ≤1:= by
    rw [div_mul_eq_mul_div, div_le_one b0]; exact budget
  have h:=WilsonOlderFreshGraphArmada.original S W C σ paid legal d0 A σ0 cap (w/b)
    (div_pos gain b0) one qo seats1 ds
  refine ⟨h.toMinistry,fun _=>gain,?_,h.purchases,h.honor⟩
  intro x
  have sum:=budget_scale b0.le (h.suggests x)
  have eq: (fun z:Name W=> if (M z).center=x then Poly.toll (fun _:Unit=>w) (M z).mode*(M z).height σ else 0)
      = fun z=>b*(if (M z).center=x then Poly.toll (fun _:Unit=>w/b) (M z).mode*(M z).height σ else 0):=by
    funext z
    have singleton (v:ℝ):Poly.toll (fun _:Unit=>v) (M z).mode=v:=by
      change (∏ _i∈S.mode.val,v)=v
      simp [full_mode S]
    rw [singleton,singleton]
    split_ifs
    · field_simp
    · simp
  rw [eq]
  simpa using sum

theorem radius (b:ℝ)(b0:0<b) (B:ℝ) (nonneg:0≤B) :
    ∃ w:ℝ,0<w ∧ w*B≤b ∧ w⁻¹=(1+B)/b:=by
  have z:0<1+B:=by linarith
  refine ⟨b/(1+B),div_pos b0 z,?_,by simp⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ z).2
  linarith
end YM.Integration.WilsonOlderFreshGraphWallet
end
