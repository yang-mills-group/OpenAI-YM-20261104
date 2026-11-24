import YM.FormalOPE.RG10.Shutters.Awning
/-! Formal parity through shifts at position probes. Choose parity-equivariant diagnostics when
assigning the tests. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
  InversionTop Orb Chart LatticePT RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {I Q :Type*}[Fintype I](w:I→ℕ){shape:Q→ℕ}
local notation "ℳ" => Mark I shape
local notation "t"=>glow shape
local notation "ins"=>PertExtension.Position.insert I shape
local notation "Λ"=> slots shape w
variable (E:TestSystem I Q shape)

structure Blinds : Prop where
 baseline : glass w E.baseline=E.baseline
 dark : ∀u∈E.Z, glass w u∈E.Z
 even (x: Mark I shape→ℝ): (E.select ((glow shape w x) ∘ markIn E.tests)).val = glass w (E.select (x∘ markIn E.tests)).val
 calm : glass w E.target.val= E.target.val

namespace Blinds
variable {w E}

local notation "Z" => E.Z
variable (L : Blinds w E)
include L

def mirror : Z→ₗ[ℝ] Z := (glazed w).restrict (show _ ≤ (Z).comap (glazed w) from fun _ h=> L.dark _ h)

lemma constant (z : Z)(f: ℳ→ ℝ) (h: (t) w f=f): E.lieResult (f ∘ markIn E.tests) (L.mirror z)= L.mirror (E.lieResult (f∘ markIn E.tests) z) := by
 apply Subtype.ext; unfold TestSystem.lieResult; rw [TestSystem.result_eq,TestSystem.result_eq];
 change _=glass w (E.select _).val; rw [← L.even]; congr 3; -- glue
 rw [← posed shape w,h, glass_add,L.baseline]; rfl

lemma stack_kind (A : ℳ → fps)(h: snooze shape w A=A) (hv:E.Regular (constantCoeff ∘ A)) : doze w (E.position A)= E.position A:= by
 let a:= E.position A; refine E.uniqueness hv ?_ ?_ ?_ ?_; rotate_left
 -- `uniqueness` constant clauses order? Lean info
 · intro i j; have he:= congr_fun₂ (ray w a 0) i j
   change constantCoeff _ = _
   rw [← coeff_zero_eq_constantCoeff_apply]; simpa [lapse,glass,a,L.baseline] using he
 · intro i j; rw [E.position_zero]
 · intro n hn
   have he:= E.positive_variation A n hn.ne'; let y : FrameAt I ℝ:=fun i j=> coeff n (a i j)
   change (y-(fun i j=>coeff n (doze w a i j)))∈ Z
   rw [ray]; exact E.Z.sub_mem he (E.Z.smul_mem _ (L.dark _ he))
 intro n; apply Subtype.ext; let H:=ins A a; let T (u:FrameAt I fps)(i:ℕ):= E.response A u i
 have ht : ins A (doze w a)= snooze shape w H:= by rw (occs:=.pos [1]) [← h]; exact gaze_transition ..
 unfold TestSystem.response; rw [ht];
 let p(x):= coeff n (H x)
 have he : (fun v=> coeff n (snooze shape w H (markIn E.tests v)))=lapse (S:=ℝ) n •(((t) w p)∘ markIn E.tests):= funext fun i=> (congr_fun (glance shape w H n) _)
 rw [he,map_smul]; change lapse (S:=ℝ) n • ((E.select _).val)=(T a n).val
 have hy : (E.select (p ∘ markIn E.tests))= E.response A a n:= rfl
 rw [L.even,hy]; unfold T a; rw [E.normalizes hv]; split <;> rename_i hu
 · simp [hu,L.calm]
 simp only [ZeroMemClass.coe_zero]; have he : glass w (0:FrameAt I ℝ)=0 := map_zero (glazed w); rw [he, smul_zero]
end Blinds
end YM.FormalOPE.RG10.Shutters
