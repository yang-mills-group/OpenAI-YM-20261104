import YM.FormalBulk08.Trellis.Ember
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Trellis
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{I J Z:Type}{K:KernelChoices}{P:Pence}
lemma bottomless (a:Pence): coeff 0 (X*a)=0:=by rw [coeff_zero_eq_constantCoeff_apply,map_mul, constantCoeff_X,zero_mul]

def flow (K:ℕ→Pence)(i k:ℕ): Pence→+* Pence:= (substAlgHom (R:=ℝ) (tribe (bottomless (expanse K i k)))).toRingHom
lemma flows (K:ℕ→Pence)(i k:ℕ)(A:Pence): flow K i k A= A.subst (X*expanse K i k):= by unfold flow; change substAlgHom _ _ = _; rw [coe_substAlgHom]
lemma from_self (K:ℕ→Pence)(k:ℕ)(A:Pence): flow K k k A=A:=by rw [flows,fill_expanse,mul_one];simp
lemma topcoin (K:ℕ→Pence)(k i)(A:Pence): coeff 0 (flow K k i A)= coeff 0 A:=by rw [flows, peep (bottomless _)]
lemma next_level (K:ℕ→Pence)(k i:ℕ)(A:Pence): flow K k (i+1) A= flow K k i (A.subst (runic (K i))):=by
   rw [flows,flows,subst_comp_subst_apply (tribe (runic_phi _)) (tribe (bottomless _))]; apply congr_arg (fun y:Pence=>PowerSeries.subst y A)
   rw [expanses_link K k i,←forward_green,propel,subst_mul (tribe (bottomless _)), subst_X (tribe (bottomless _)),mul_assoc]
lemma prev_level (K:ℕ→Pence)(k i:ℕ)(A:Pence): flow K k i A= flow K k (i+1) (A.subst (wake (K i))):=by rw [next_level,subst_comp_subst_apply (tribe (wake_phi _)) (tribe (runic_phi _)),back_merge];simp
lemma chamber_flow (K:ℕ→Pence)(k)(i): (flow K k i).comp (flow K i k)= RingHom.id Pence:= by
    -- ratio global: flow acts group forms on p; show composition K k i • K i j equals K k j for ANY j by induction along nearest
    suffices h :∀ j,(flow K k i).comp (flow K i j)= flow K k j by rw [h];ext1 x; exact from_self K _ _
    have ht:(flow K k i).comp (flow K i i)=flow K k i:= RingHom.ext fun x=> by change flow K k i (flow K i i x)=_;rw [from_self]
    have hh (j:ℕ)(hp:j≥ i):(flow K k i).comp (flow K i j)=flow K k j := by
       induction hp with
       | refl=> exact ht
       | @step j hp ih=> ext1 x; rw [RingHom.comp_apply,next_level K i j,next_level K k j]; exact DFunLike.congr_fun ih _
    intro j; by_cases hu:i≤j;exact hh j hu
    have hp : j ≤ i:=by omega
    clear hu; induction hp using Nat.decreasingInduction with
    | self=>exact ht
    | of_succ j hj ih=> ext1 x; rw [RingHom.comp_apply,prev_level K i j, prev_level K k j]; exact DFunLike.congr_fun ih _
lemma fresh_expanse (K:ℕ→Pence) (i j): Fresh (expanse K i j) := by
   have hp:Fresh (expanse K i i):= by rw [fill_expanse]; exact coeff_zero_one
   by_cases he:i≤ j
   · induction he with
     | refl=> exact hp
     | step hl ih=> rw [expanses_link]; exact fuel_fresh (book_fresh _) ih
   have he':j≤ i:=by omega
   clear he; induction he' using Nat.decreasingInduction with
   | self=> exact hp
   | of_succ k hk ih=> rw [expanses_reverse]; exact fuel_fresh (fresh_N _) ih
-- profiles/stir & joint ratio changes. Nextpay uses only static salts.
variable {s w :Z→ℕ}{δ:Z→ℝ}{T U:Z→Pence}{τ:Time Z}{Y M:Z→ℕ→Pence}{E:ℕ}
lemma priced_flow (h: Priced τ δ T U E)(he:Priced τ δ (fun i=>expanse (Y i) (s i) (w i)) (fun i=>expanse (M i) (s i) (w i)) E): Priced τ δ (fun i=> flow (Y i) (s i) (w i) (T i)) (fun i=>flow (M i) (s i) (w i) (U i)) E:= by simp_rw [flows]; exact h.by_order ((transit he).le (Nat.le_succ _)) (fun i=>bottomless _) (fun i=>bottomless _)

variable [Fintype I][DecidableEq I]
def ropes (K:ℕ→Pence)(T:ℕ→Pennants I)(k j l :ℕ) : Pennants I:= propels (fun a=> ((T (j+a))⁻¹).map (flow K k (j+a))) 1 l
lemma ropes_grow (K:ℕ→ Pence)(T:ℕ→Pennants I)(k i n:ℕ): ropes K T k i (n+1) = Matrix.map ((T (i+n))⁻¹) (flow K k (i+n)) * ropes K T k i n:=by rw [ropes,propels];rfl
lemma ropes_split (K:ℕ→ Pence)(T:ℕ→Pennants I)(k i m n:ℕ): ropes K T k i (m+n)=ropes K T k (i+m) n * ropes K T k i m:= by
   induction n with
   | zero=> rw [Nat.add_zero,show ropes K T k (i+m) 0=1 from rfl,one_mul]
   | succ n ih=>rw [←add_assoc m n,ropes_grow,ropes_grow,←add_assoc i m,ih, mul_assoc]
-- n is length, transforms semi-linear
omit [Fintype I] in
lemma pours {T: Pennants I}{r w:I→ℕ}{b:I→ℝ}(h:Found r w T b)(K:ℕ→Pence)(i k): Found r w (T.map (flow K k i)) b:= by
    refine ⟨fun x y p=>(topcoin K k _ _).trans (h.bound x y p),h.scale, fun x y p q=>(topcoin K k _ _).trans (h.label x y p q)⟩
end YM.FormalBulk08.Trellis
