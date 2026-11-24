import YM.OPE.Compatible.Streams.Farm
/-!
# The base deck. φ(grade flags) virtual. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}
structure Aeon (W:Type)(T:(i:Fin s)→Cuts d μ v b (E i) G)(X:S!→L[ℝ] S!)(u:W→ℝ) where
    flag : ℕ→ W→ Submodule ℝ (Mints E)
    read (i:ℕ)(hi:i<d)(w:W): flag i w→ₗ[ℝ] Fruition X (μ i)
    first (i:W):flag 0 i=⊤
    moves (i:ℕ)(w:W)(he:i<d): flag (i+1) w≤ flag i w
    depth (i:ℕ)(w:W)(hi:i<d)(p:flag i w): p.val∈ flag (i+1) w ↔ read i hi w p=0
    quake(i:ℕ)(hi:i<d)(w:W)(p:flag i w)(z:Fin s)(hz:trims z.val p.val):
        p.val z∈(T z).flag i ∧ trims z.val (read i hi w p).val∧(T z).Tap i ((read i hi w p).val z)=(T z).Tap i (p.val z)
    price(i:ℕ)(hi:i<d):∃ C:ℝ,0≤C∧∃ k:ℕ,∀ w p,‖(read i hi w p).val‖≤ C*u w^k*‖p.val‖
    non : 1≤ u
variable {V W:Type}{w p':V→ℝ}
namespace Aeon
variable (A:Aeon V T X w)
local notation "F!"=> Fruition X (μ k)
lemma bulk (hk:k<d)(f:∀ i,A.flag k i)(hp: Wealth (fun i=>(f i).val) w p'): Wealth (fun i=>(A.read k hk i (f i)).val) w p':=by
     obtain ⟨c,hc,k,H⟩:=A.price k hk; obtain ⟨b,hb,j,h⟩:= hp; refine ⟨c*b,mul_nonneg hc hb,k+j,fun i=> ((H i (f i)).trans (mul_le_mul_of_nonneg_left (h i) (mul_nonneg hc (pow_nonneg (le_trans zero_le_one (A.non i)) _)))).trans_eq ?_⟩; rw [pow_add]; ring
noncomputable def branch (t:W→ V):Aeon W T X (w∘t):=⟨fun k i=>A.flag k (t i),fun k hk i=>A.read k hk (t i),fun i=>A.first (t i),fun k i hk=>A.moves _ _ hk,fun k i hk=> A.depth k (t i) hk,fun k hk i=> A.quake k hk _,fun i hi=>by obtain ⟨a,ha,l,h⟩:=A.price i hi; exact ⟨a,ha,l,fun i=>h (t i)⟩,fun i=>A.non (t i)⟩
end Aeon
namespace Eave
variable {θ:ℕ→ℝ}{r:ℕ→ℝ}{L:H→ℕ→ Mints E→L[ℝ] Mints E}
end Eave
end YM.OPE.Hark
