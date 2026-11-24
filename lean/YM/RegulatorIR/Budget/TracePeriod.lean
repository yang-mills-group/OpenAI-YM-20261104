import YM.RegulatorIR.Budget.TraceCopy

/-! Identify the discrepancy as just a loop with `repeatK - primary`. The
volumes and anchor convention in both types of periodization are exact at
this point. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget
open Set Function Tuple Deck Layer Packet Motion Spatial Copies
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y : Type} {r : ℕ} {P:ℝ} (A: Deck P X Y)

lemma loop_lodge {T:Packet X (r+2)} (h:A.Ready T) (K: Layer Y Y) {s:Tariff X} {a b:ℝ≥0∞}
    (hh:localQ s T a)(ha:a ≠ ⊤)(H:height K b)(hb:b ≠ ⊤)(z: Tuple Y r)(i:Fin r)(x:X) (hx:A.orbit x=z i):
      loop (A.deckSum T) K z=A.lodge (loop T (repeatK A K)) z i x := by
 apply schema A T z (Subtype.val : Nest A z i x→_) (nest_summable A hh ha z i x) (A.deckSum T) K H hb
 intro p
 rw [A.deck_pivot h (linked z p) i.succ.succ x (hx.trans (link_here ..).symm)]
 unfold Stalk.collect lodge; rw [← (decompression A z i x p).tsum_eq]
 rfl
lemma loop_scroll {T:Packet X (r+2)} (K:Layer Y Y){a:ℝ≥0∞}(hh: Summable T)(ha:a ≠ ⊤)(H:height K a)(z:Tuple Y r):
    loop (A.scroll T) K z=A.scroll (loop T (repeatK A K)) z:= by
 apply schema A T z (Subtype.val : Stalk A.project z→_) (stalk_summable A hh z) (A.scroll T) K H ha
 intro p; unfold Deck.scroll Stalk.collect; rw [← (compression A z p).tsum_eq];rfl
lemma loop_gap_lodge {T:Packet X (r+2)} {K:Layer X X}(Z:Layer Y Y){l:Tariff X}{a b c:ℝ≥0∞} (h:Layer.Sym A A K) (H:A.Ready T)
    (hx:localQ l T a)(ha:a≠⊤)(hf:height K b)(hb:b≠⊤)(hz:height Z c)(hc:c≠⊤)(q:Tuple Y r)(i:Fin r)(v:X)(hv:A.orbit v=q i):
     (loop (A.deckSum T) Z - A.deckSum (loop T K)) q=A.lodge (loop T (repeatK A Z-K)) q i v:= by
 rw [Pi.sub_apply, loop_lodge A H Z hx ha hz hc q i v hv,A.deck_pivot (loop_ready H h) q i v hv]
 exact cost_sub A T (Subtype.val : Nest A q i v → _) (nest_summable A hx ha q i v) _ _ (repeat_cap A hz) hf hc hb
lemma loop_gap_scroll {T:Packet X (r+2)} {K:Layer X X}(Z:Layer Y Y){a b:ℝ≥0∞}
    (hh:Summable T) (hp:height K a)(ha:a≠⊤)(ht:height Z b)(hb:b≠⊤):
     loop (A.scroll T) Z - A.scroll (loop T K) = A.scroll (loop T (repeatK A Z-K)):= by
 ext1 q; rw [Pi.sub_apply,loop_scroll A Z hh hb ht]
 exact cost_sub A T (Subtype.val : Stalk (fun p:Tuple X r=>A.project p) q → _) (stalk_summable A hh q) _ _ (repeat_cap A ht) hp hb ha
end YM.RegulatorIR.Budget
