import YM.FormalBulk08.Dove.Host

/-! Numerical cost functions one implementation (the recurrence need not
know these choices). Steering interface accepted tasks can combine; BEFORE
widths then lengths, only afterwards postage. θ still independent branch. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable (G: Gauge)(K:KernelChoices){t j m E:ℕ}

def window (t:ℕ):ℝ:= if h:4≤t then (flax_width G K.penalty K.penalty_pos h).choose else 1
def joint (t j:ℕ):ℝ:= if h:4≤t∧ 5≤j then (holidays K G h.2 h.1).choose else 1
lemma window_pos (t):0<window G K t:= by
    unfold window;split
    case isTrue h=> exact (flax_width G K.penalty K.penalty_pos h).choose_spec.1
    case isFalse h=> norm_num
lemma joint_pos (t j):0<joint G K t j:= by
    unfold joint;split
    case isTrue h=> exact (holidays K G h.2 h.1).choose_spec.1
    case isFalse h=> norm_num
lemma window_le (t):window G K t≤1:= by
    unfold window;split
    case isTrue h=>exact (flax_width G K.penalty K.penalty_pos h).choose_spec.2.1
    case isFalse h=> exact le_rfl
variable {G K}
lemma head_fee (E:ℕ){σ:ℝ}(h:4≤t)(he:0<σ)(hz:σ≤window G K t):∃ C:ℝ,Flax G K.penalty t E σ C:= by rw [window,dif_pos h] at hz;exact (flax_width G K.penalty K.penalty_pos h).choose_spec.2.2 E σ he hz
lemma pair_fee {σ η A:ℝ}(h:4≤t)(hx:5≤j)(p:0<σ)(u:0<η)(he: η ≤ joint G K t j)(hb:0≤A)(ρ:ChartRatio G)(E:ℕ): ∃ W:ℝ,0<W∧Holidays K σ η A W ρ j t E:= by rw [joint,dif_pos (And.intro h hx)] at he; exact (holidays K G hx h).choose_spec.2 σ η A p u he hb ρ E
-- prices first. no keyword costs on prerequisite σ ≤...
variable (G K)
def cost0 (σ:ℝ)(j E:ℕ):ℝ:= if h:4≤j ∧ 0<σ∧ σ≤window G K j then (head_fee E h.1 h.2.1 h.2.2).choose else 0
variable {G K}
lemma cost0_use {σ:ℝ}(h:4≤j)(p:0<σ)(hu:σ≤window G K j):Flax G K.penalty j E σ (cost0 G K σ j E):= by rw [cost0,dif_pos ⟨h,p,hu⟩]; exact (head_fee E h p hu).choose_spec
variable (G K)
def costL (σ η A:ℝ)(ρ:ChartRatio G)(t j E:ℕ):ℝ:= if h: 4≤t ∧ 5≤j ∧ 0<σ∧0<η∧η≤joint G K t j∧ 0≤A then (pair_fee h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 ρ E).choose else 0
variable {G}
lemma costL_use (t j E:ℕ){σ η A :ℝ}(h:4≤t)(hx:5≤j)(p:0<σ)(u:0<η)(he:η ≤joint G K t j)(hb:0≤A)(ρ:ChartRatio G): Holidays K σ η A (costL G K σ η A ρ t j E) ρ j t E:= by rw [costL,dif_pos ⟨h,hx,p,u,he,hb⟩]; exact (pair_fee h hx p u he hb ρ E).choose_spec.2

def labelC (σ η A:ℝ)(ρ:ChartRatio G)(t E:ℕ)(P:Patch)(V:Lodge P):ℝ:= if h:4≤t ∧ 5≤P.J∧ 0<σ∧0<η∧η≤joint G K t P.J∧0≤A ∧ costL G K σ η A ρ t P.J E ≤ (P.L.val:ℝ) then ((costL_use K t _ E h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 ρ) P rfl h.2.2.2.2.2.2 V).choose else 0
lemma label_cert {σ η A : ℝ}(ρ:ChartRatio G)(P:Patch)(h:4≤t)(hx:5≤ P.J)(p:0<σ)(u:0<η)(he:η≤joint G K t P.J)(hb:0≤ A)(hl:costL G K σ η A ρ t P.J E ≤ (P.L.val:ℝ))(V:Lodge P): Credentials K t P V σ η A (labelC K σ η A ρ t E P V) ρ E:= by rw [labelC,dif_pos ⟨h,hx,p,u,he,hb,hl⟩]; exact ((costL_use K t _ E h hx p u he hb ρ) P rfl hl V).choose_spec

-- one template given before every length choice. Demonstrate no demand on width
-- of an infinitely often preceding stage. Other templates may choose smaller.

def shining (G: Gauge)(t:ℕ):ℝ:= min (min (window G K t) (joint G K t t)) (joint G K t (t+1))
lemma shining_pos (G:Gauge) (t): 0<shining K G t:=lt_min (lt_min (window_pos ..) (joint_pos ..)) (joint_pos ..)
lemma shining_win (G:Gauge)(t): shining K G t ≤ window G K t:=(min_le_left ..).trans (min_le_left ..)
lemma shining_join (G:Gauge)(h:t≤j)(ht:j≤t+1): shining K G t ≤joint G K t j:= by
   have h': j=t ∨ j=t+1:=by omega
   rcases h' with H|H <;> rw [H]
   · exact (min_le_left ..).trans (min_le_right ..)
   exact min_le_right ..
-- Realized integer requires applicant ensures ≥..., kernel G widths positive; pair L depends on no realised future L or history. worst two neighbor cases.
def commonBill (w:ℕ→ℝ)(ρ:ChartRatio G)(j E:ℕ):ℝ:=
    max (costL G K (w j) (w j) (cost0 G K (w j) j E) ρ j j E) (costL G K (w j) (w (j-1)) (cost0 G K (w (j-1)) (j-1) E) ρ (j-1) j E)
lemma common_due (w:ℕ→ℝ)(ρ:ChartRatio G)(h:t≤j)(ht:j≤t+1): costL G K (w j) (w t) (cost0 G K (w t) t E) ρ t j E ≤ commonBill K w ρ j E := by
    rcases Nat.eq_or_lt_of_le h with h|h
    · subst t; exact le_max_left ..
    have ht': t=j-1:= by omega
    rw [ht']; exact le_max_right ..
end YM.FormalBulk08.Dove
