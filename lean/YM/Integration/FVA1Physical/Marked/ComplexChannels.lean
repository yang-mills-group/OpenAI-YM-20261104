import YM.Integration.FVA1Physical.Marked.WalletMask
import YM.Integration.FVA1Physical.Marked.JointSource

/-! Reconstruct complex mixed modes from the actual real wallet, before
taking any norm. Cancellations survive the independent singleton masks. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Multi Qlocal Quipu Quipu.Sonnet Tern Moonset MeasureTheory
open MergeProof.Accent Extra.Trajectories LocalLTE.Sail
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I}

def component (T : Finset I) (j : I) : ℂ →ₗ[ℝ] ℝ :=
  if j∈T then Complex.imCLM.toLinearMap else Complex.reCLM.toLinearMap

def complexWallet (A : Finset I→Poly B) : Poly B := fun s=>
  ∑ T∈s.val.powerset, Complex.I^T.card * (A T).part s

/-- The complex coefficient of a multi-insertion is reconstructed exactly
from real source inputs, with the empty mode fixed. -/
theorem component_product (S : Finset I) (F : I→ℂ) :
    ∑ T∈S.powerset,Complex.I^T.card * (∏ j∈S,(component T j (F j):ℂ)) = ∏ j∈S,F j := by
  have separ (j : I) : F j = Complex.I*(F j).im + (F j).re := by
    rw [add_comm,mul_comm,Complex.re_add_im]
  conv_rhs => rw [Finset.prod_congr rfl (fun j _=>separ j),Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT=>?_
  have sub : T⊆S := Finset.mem_powerset.mp hT
  have left : ∏ j∈T,(component T j (F j):ℂ) = ∏ j∈T,((F j).im:ℂ) := Finset.prod_congr rfl (by
    intro j hj; simp only [component,if_pos hj]; rfl)
  have right : ∏ j∈S\T,(component T j (F j):ℂ) = ∏ j∈S\T,((F j).re:ℂ) := Finset.prod_congr rfl (by
    intro j hj; simp only [component,if_neg (Finset.mem_sdiff.mp hj).2]; rfl)
  rw [← Finset.prod_sdiff (f:=fun j=>(component T j (F j):ℂ)) sub,left,right,
    Finset.prod_mul_distrib,Finset.prod_const]
  ring

variable [Fintype I] {G : Gauge} {H : History G} {N n : ℕ} {b d : ℕ} {ξ : I→ℕ}
    {o : I→Site (H.S.side N n)} {P : Rep G (H.S.side N n)}
    (W : Rooms.Wallet (Finset I) o P B ξ d b) (cut : ℕ) (g : ℝ) (Y : Batch H N n I)
    (isolated : ∀ t (s : Senses B), 2 ≤ (essence s).card → W.weight t s=0)
    (realized : ∀ t j u,bareLeaf W t cut g j u = component t j (Y.wavelengths j u))

def complexSeed (W : Rooms.Wallet (Finset I) o P B ξ d b) (cut : ℕ) (g : ℝ)
    (v : Config G (H.S.side N n)) : Poly B :=
  complexWallet (fun t=> (((H.rep N n N).eval v):ℂ) • Poly.pass (W.render cut g t v))

include isolated realized in
/-- Each mixed mode of the recombined native input is precisely the true
physical insertion, or zero when a marker in that mode fails. No triangle
inequality or combinatorial multiplicity is used during recombination. -/
theorem complex_masked_mode (v : Config G (H.S.side N n)) (s : B.Mode) :
    (complexSeed (H:=H) (N:=N) (n:=n) W cut g v).part s =
      if ∀ j∈s.val,Healthy P.p.threshold (Tale.court P.p.B (o j)) v then (Y.raw B v).part s else 0 := by
  let healthy := fun j=>Healthy P.p.threshold (Tale.court P.p.B (o j)) v
  let vac := ((H.rep N n N).eval v:ℂ)
  let x := fun j=>Y.wavelengths j v
  have part (t : Finset I) : (vac • Poly.pass (W.render cut g t v)).part s =
      vac*∏ j∈s.val, if healthy j then (component t j (x j):ℂ) else 0 := by
    rw [Poly.part_smul,singleton_render W t cut g (isolated t),Mach,pass_fire]
    congr 1
    exact Finset.prod_congr rfl (fun j _=>by simp only [realized,x,healthy])
  change (∑ t∈s.val.powerset,Complex.I^t.card*(vac • Poly.pass (W.render cut g t v)).part s) = _
  simp_rw [part]
  by_cases hs:∀ j∈s.val,healthy j
  · rw [if_pos hs]
    have eq (t : Finset I) : (∏ j∈s.val, if healthy j then (component t j (x j):ℂ) else 0) =
        ∏ j∈s.val, (component t j (x j):ℂ) := Finset.prod_congr rfl fun j hj=>if_pos (hs j hj)
    simp_rw [eq,mul_left_comm (Complex.I^_) vac]
    rw [← Finset.mul_sum,component_product]
    change _ = (vac • Poly.pass (Mach B (fun j=>x j))).part s
    rw [Poly.part_smul,Mach,pass_fire]
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨j,hj,hbad⟩ := hs
    apply Finset.sum_eq_zero
    intro t _
    rw [Finset.prod_eq_zero hj (if_neg hbad),mul_zero,mul_zero]

end YM.Integration.FVA1Physical.Marked
