import YM.OPE.Compatible.Juniper.Cone
/-!
# Live supports
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
variable {p:Song (Scoop G b)}
noncomputable def Locket (h:ReadyP p i) (m:ℕ) :bed G i m:=
     ⟨fundus (ShapeX p) _ (TomX m i p h),fun j=> by rw[sproutsX]; obtain ⟨hp,hT⟩:= TickY _ (h.finance.2 j) (h.Hue j); exact ⟨⟨_,(TomX m i p h).2 _⟩,Pacing _, hT,hp⟩⟩
variable {τ:Char.Phase→ℕ}
lemma dosh (h:ReadyP p i) : ‖Locket h m‖ ≤ billP i b m p:= sproutsU _ (TomX m _ _ h)
noncomputable def ChiselV (H:Aware i τ)(h:ReadyP p i): solar G i τ:= crestL G H 0 (Locket h (τ 0))
lemma WarmCost (H:Aware i τ)(h:ReadyP p i): ‖ChiselV H h‖ ≤ ‖crestL G H 0‖ * billP i b (τ 0) p:=by unfold ChiselV; exact ( (crestL G H 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left (dosh h) (norm_nonneg _))
lemma Weft (H:Aware i τ)(h:ReadyP p i): spread G i τ (ChiselV H h).val=∑ j:Fin (i+1),Grid.lance (ShapeX p j.val):=by
      let L:=Locket h (τ 0); change Drift.spread G i τ (ascendF G H 0 L)= _; rw [show Drift.spread _ _ _ _= baby (τ:=τ) (d:=i) 0 L.val from pick G H 0 L]; unfold baby; change (∑ j:Fin (i+1),Drift.glide (Grid.lance (lilies (τ 0) i (Shade G) L.val j.val)) 0)= _; rw [show lilies (τ 0) i _ L.val=ShapeX p from sproutsX _ (TomX (τ 0) _ _ h)]; exact Finset.sum_congr rfl fun j _=>by ext1 t; fin_cases t <;> rfl -- computational if tests
lemma PeekB (H:Aware i τ)(h:ReadyP p i): (ChiselV H h).val 0=(Locket h (τ 0)).val:= (crestP G H _ _).1 -- enhance
section
variable (p)
local notation "F!"=>ShapeX p
-- support capacity: stamp based
abbrev PinB (b k:ℕ) := 1+(k+2)*((2*k+3)*(1+k*(4*(4*b))))
lemma Nest_Q (j d:ℕ)(hv:j ≤ d)(t:Phase) (r:ℕ)(i:Page (Shade G) r)(hh:Grid.lance (F! j) t r i ≠ 0): stamp i ≤ PinB b d:=by
      have hp: r=j+t.val:= by by_contra ht; have hC: Grid.lance (ShapeX p j) t r=0:=hubbub ht; rw[hC] at hh;exact hh rfl
      subst r; have he: timbre ships (F! j) _ i≠0:= (show Shell.throw (timbre ships (F! j) _) (j+t.val)=_ from Pi.single_eq_same ..) ▸ hh -- proof
      obtain ⟨u,ha⟩:= Function.ne_iff.mp (show (fun k=> F! j k*coff (ships k) (j+t.val) i)≠(fun _=>0) from fun h=>he (by unfold timbre;rw [h];simp)); have ht: (F! j u)≠0:=fun hp=>ha (by rw [hp,zero_mul]); have hQ:u∈encircled G (4*b) j:=not_not.mp fun hp=>ht (HoneyOut _ _ hp)
      have hk:i∈rim (ships u) (j+t.val):=not_not.mp fun hp=>ha (by rw [stair _ hp,mul_zero])
      obtain ⟨v,hh,hS⟩:=Finset.mem_image.mp hQ; have hu: stamp u ≤1+j*(4*(4*b)):=by
           rw [← hS,perimeter]; apply Nat.add_le_add_left _ _; exact (Finset.sum_le_sum (f:=fun i:Fin j=> Laurent.size (CageB _ _ v i).1) (fun i _=> bounded (v i|>.1.property.1))).trans_eq (by simp)
      let L:=lawn (ships u); have hz:=supportM u; refine (rimS _ _ hk).trans (add_le_add_right (mul_le_mul (by have h:=t.isLt;omega) (Nat.le_trans (Nat.le_of_succ_le hz) (mul_le_mul (by omega) (le_trans hu (by gcongr)) (Nat.zero_le _) (Nat.zero_le _))) (Nat.zero_le _) (Nat.zero_le _)) 1) -- parameters
abbrev coveredM (Q: Muse G)(i:ℕ):= ∀ (t:Char.Phase) (k:ℕ)(p:Page (Shade G) k), Q t k p≠0 → stamp p ≤ i
lemma Root_Q (H:Aware i τ)(h:ReadyP p i): coveredM (spread G i τ (ChiselV H h).val) (PinB b i):=by
      rw [Weft]; intro t j u hu; by_contra hh; apply hu; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_eq_zero fun k _=>not_not.mp fun hz=> hh (Nest_Q p k.val i (by omega) t j u hz)
end
end YM.OPE.Spells
