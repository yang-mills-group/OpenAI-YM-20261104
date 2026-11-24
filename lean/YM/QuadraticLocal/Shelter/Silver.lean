import YM.QuadraticLocal.Shelter.Animal
import YM.QuadraticLocal.Shelter.Shine
/-! # Bind clear passthrough to the exact Spire.postGlobal term at input momentum -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals QuadraticLocal.Spire
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink QuadraticLocal.Shelter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {a e σ r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)
namespace Width
set_option quotPrecheck false
open Club Promote Press Accumulate Scene
variable (B W:BudgetPoint)(S:StepData c n) (g:ℝ)
local notation "Q'"=> Width.quiet X S.ratio W g
local notation "U₀"=> rendered X B g
lemma passe (t:α)(v:Config G c):(Width.quiet X S.ratio W g).log t v=(convertGlobal (rendered X B g) S W).log t v:=by
    let Q:Solo.Watching X→Poly R:= fun j=>(Q').frame j t v
    let V:Solo.Watching X→Poly R:= fun j=>(convertGlobal (U₀) S W).frame (⟨j.val,j.prop⟩:Waves U₀) t v
    have hv (j:Solo.Watching X): Q j=V j:=by
        unfold Q V; rw [Spire.frame U₀]; apply congr_arg (Poly.send (X j.val).mode) (show (Q').light t j v=(U₀).light t j.val 1 from ?_)
        unfold Lamps.light; rw [if_pos (show (Q').clear j from j.prop), if_pos (show (U₀).clear _ from j.prop)]; exact Solo.reads (X j.val) S.ratio j.prop t v
    -- avoid reducibility stuck by explicit terms
    change (∑' j:Solo.Watching X, Q j) = ∑' j:Solo.Watching X, V j
    exact tsum_congr hv

end Width
end YM.QuadraticLocal.Earn
