import YM.Pier.Reserve.Graph
/-! Erase the FORCED INPUT (for comparison ONLY on the stocks fed into the local computation).
The iterated result will live again in the complete, retained `Coin` norm, not the
projected one. No comparison of changing unmarked K symbols in this projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Finset Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Bid
  Extra.Histories Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
  MergeProof MergeProof.Matric MergeProof.Matric.Gram
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
section gauge
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d} {Y:Hol G} {t:Side}{D:Desk G t} {x: F.Coeff}
variable {R:Rep G t} {p:File G t} {q κ : ℝ} {b c : ℝ}

private theorem remove_bound
    (h:Tab (book x p) 0 R κ b c) : Tab (book x (p.1,0)) 0 R κ b 0 := by
  refine ⟨h.divisor,h.first,le_rfl,h.regular,fun i=>0, by rw [mul_zero]; exact budget0 ..,
    fun i=>⟨le_rfl,fun U=> by simp⟩⟩

private lemma okE (p:Coin F Y D): Pay F Y D ((Coin.uses p).1,0) ‖p‖ := by
   obtain ⟨h,he⟩:= Coin.wealth p
   constructor
   · exact ⟨h.smooth,h.origin,h.identity_null,h.projects,fun i U h' => False.elim (h' rfl),
       fun i h'=>False.elim (h' rfl),fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
   obtain ⟨a,b,hv,hb⟩:= rem_tabs.mp he
   exact (remove_bound hv).bound ((add_le_add le_rfl hv.second).trans hb)

def eject : Coin F Y D →ₗ[ℂ] Coin F Y D where
    toFun p:= Coin.saver F Y D ((Coin.uses p).1,0) (okE p)
    map_add' f g := by apply Coin.noted; simp only [map_add, Coin.use_save]; ext <;> simp
    map_smul' x f := by apply Coin.noted; simp only [map_smul, Coin.use_save]; ext <;> simp

lemma literal (p:Coin F Y D): Coin.uses (eject p) = ((Coin.uses p).1,0) := rfl
lemma contract (p:Coin F Y D): ‖eject p‖ ≤ ‖p‖:= (Coin.wealths _).mpr (literal p|>.symm ▸ okE p)
lemma deficient (p:Coin F Y D): Coin.uses (p-eject p)= (0,(Coin.uses p).2) := by
  rw [map_sub,literal]; ext <;> simp
private theorem forced_bound
    (h:Tab (book x p) 0 R κ b c) : Tab (book x (0,p.2)) 0 R κ 0 c :=
    ⟨h.divisor,le_rfl,h.second,⟨0,budget0 ..,fun _=>(regular0 ..).2⟩,h.forced⟩

def soft (Q:Gram F Y D q) : Gram F Y D q where
    g:= eject ∘ₗ Q.g
    toll _:= (contract _).trans (Q.toll _)
lemma soft_axis (Q:Gram F Y D q) (i:F.Index) : (soft Q).scythe i=eject (Q.scythe i):=rfl
lemma soft_stable (Q U:Gram F Y D q) (hp: Q.Within U b) : (soft Q).Within (soft U) b :=
  ⟨hp.1,fun i=> by
    change ‖eject (Q.g i)-eject (U.g i)‖ ≤ _
    rw [← map_sub]
    exact (contract _).trans (hp.2 i)⟩

end gauge

section bound
variable {G:Gauge} {d:ℕ} {F:Labels.Frame G d} {H:History G} {N p j:ℕ} {Y:Hol G}
variable {W:Worth} {u ζ v C : ℝ}
variable {S:Desk G (H.S.side (j+1) p)} {E:Desk G (H.S.side j p)}
    (hw : Well (H.rep N p (j+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (j+1))))
local notation "Old"=> H.rep N p (j+1)
local notation "κ'"=> Real.sqrt (H.levels.clock.forcedAllowance (j+1))
set_option quotPrecheck false
local notation "s" => (H.levels.params (j+1)).columns

variable (Q:Gram F Y S ((H.levels.params (j+1)).columns))
include hw
lemma exposes : InRange H N p j Q (soft Q) κ' := by
  intro i
  let f := Q.scythe i
  obtain ⟨a,b,hp,hb⟩:= rem_tabs.mp (granted hw Y (Size.axis F i) f).2
  rw [soft_axis,deficient (Q.scythe i)]
  have hs : ‖f‖ ≤ s := (Q.toll _).trans
    ((mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans_eq (Size.size_axis F i))
      (zero_le_one.trans (H.levels.params (j+1)).columns_ge)).trans_eq (mul_one _)) -- trans_eq notation
  refine ⟨0,b,forced_bound hp,(zero_add _).le.trans ?_⟩
  exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hp.first).trans (hb.trans hs)) hp.divisor.le
end bound
end YM.Pier
