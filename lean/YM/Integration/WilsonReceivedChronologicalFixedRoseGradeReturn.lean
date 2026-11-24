import YM.Integration.WilsonOriginalObservedRoseSevenScale

/-! The measured proper components are recovered from the separately entered row and its paid defects.
Each cofactor spends the physical grade of its own sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGradeReturn
open Finset WilsonPositionThermometerConnected
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonOriginalObservedRoseVanePurse (ages)
open scoped Classical BigOperators
local notation "Faces" => Finset (Fin 3)

theorem original (p q:Faces→ℂ){r z τ:ℝ}(rp:0≤r)(two:2≤z)(pos:0≤τ)(small:τ≤1)(A B:ℕ)
    (low:∀s:Faces,s.Nonempty → r^(height ages s)*‖q s‖≤z^(B+A*height ages s))
    (delta:∀s:Faces,s.Nonempty → r^(height ages s)*‖p s-q s‖≤z^(B+A*height ages s)*τ):
    r^14*‖value p-value q‖≤21*z^(3*(B+1)+A*14)*τ:=by
  have hz:1≤z:=(by norm_num: (1:ℝ)≤2).trans two
  have grow (s:Faces):z^(B+1+A*height ages s)=z^(B+A*height ages s)*z:=by
    rw [show B+1+A*height ages s=B+A*height ages s+1 by omega,pow_succ]
  have non (s:Faces):0≤z^(B+A*height ages s):=pow_nonneg (zero_le_one.trans hz) _
  exact WilsonOriginalObservedRoseSevenScale.original p q rp hz pos A (B+1)
    (fun s hs=>by
      have add:‖p s‖≤‖p s-q s‖+‖q s‖:=by
        calc ‖p s‖=‖(p s-q s)+q s‖:=by rw [sub_add_cancel]
             _≤_:=norm_add_le _ _
      calc
        r^(height ages s)*‖p s‖≤r^(height ages s)*(‖p s-q s‖+‖q s‖):=
          mul_le_mul_of_nonneg_left add (pow_nonneg rp _)
        _≤z^(B+A*height ages s)*τ+z^(B+A*height ages s):=by
          rw [mul_add];exact add_le_add (delta s hs) (low s hs)
        _≤z^(B+A*height ages s)*2:=by
          nlinarith [mul_le_mul_of_nonneg_left small (non s)]
        _≤_:=by rw [grow];exact mul_le_mul_of_nonneg_left two (non s))
    (fun s hs=>(low s hs).trans (by rw [grow];exact le_mul_of_one_le_right (non s) hz))
    (fun s hs=>(delta s hs).trans (mul_le_mul_of_nonneg_right
      (by rw [grow];exact le_mul_of_one_le_right (non s) hz) pos))

end YM.Integration.WilsonReceivedChronologicalFixedRoseGradeReturn
end
