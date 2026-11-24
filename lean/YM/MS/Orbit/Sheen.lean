import YM.MS.Orbit.Rule
/-!
# Single-parameter reading. Rank clock. Linear transfer. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {I E A B C:Type}{G:Gauge}{p:Sector A}{u v:ℂ}
abbrev BL (A: Type):= Raw A ℂ
abbrev OM (A: Type):= ℝ→ BL A
abbrev Therapy (A B : Type):= BL A →ₗ[ℂ] BL B
variable {F H D U:OM A}
abbrev Lead (V:OM A)(F: BL A) (t:ℝ): Prop:=∀ w,HasDerivAt (fun t:ℝ=> V t w) ( F w ) t
structure Status (V:OM A)(F:OM A): Prop where
   life : ∃ k:ℕ,∀ t, Limit ( V t ) k
   path t: Lead V ( F t ) t
lemma prop_status {U V: over I A}(h:Modal U V)(i:I): Status ( U i ) ( V i ):= ⟨ by obtain ⟨k,H⟩:= h.cap; exact ⟨ k,H i ⟩, h.pace i ⟩
structure Glance (P:Therapy A B): Prop where
   lap F k : Limit F k→ Limit ( P F ) k
   tip F H t : Lead F H t → Lead ( P ∘ F ) ( P H ) t
lemma wheel_gl (P:Cog p)(u v:ℂ): Glance (P.wheel u v):= by
   constructor; · intro F k hF w hw; induction w generalizing F k with| nil=> rw [wheel_nil]; exact hF _ hw | cons i l ih=> rw [ D_eval i (P.wheel u v F), wheel_rule, blend_at,map_add,map_smul,map_smul]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul ]; simp only [ih _ ( k-1) (hF.tip _) (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hw; omega), mul_zero,add_zero ] -- may binder ordering ih
   intro F H t hF l; induction l generalizing F H with| nil=> simp_rw [comp_apply,wheel_nil]; exact hF []| cons i l ih=>
        simp only [ comp_apply,D_eval i, wheel_rule, blend_at, map_add,map_smul,map_smul,Pi.add_apply ]; let x:=P.mode i; have he (b:A): Lead (fun t=> D b (F t)) (D b H) t:=fun l=> hF ( b::l ); exact ((ih _ _ ( he i)).const_mul u).add (( ih _ _ (he x) ).const_mul (v*P.spin i))
lemma gl_Rid : Glance (LinearMap.id: Therapy A A):= ⟨fun _ _ H=> H,fun _ _ _=>id⟩ -- linter
lemma gl_read (S:Cog p)(b:Bool): Glance ( S.readerV b ):= by cases b; exact gl_Rid; exact wheel_gl S _ _
lemma glpto {P:Therapy A B}(hF:Glance P)(hv:Status F H): Status (P∘F) (P∘H):= ⟨ by obtain ⟨k,hk⟩:= hv.life; exact ⟨ k,fun t=> hF.lap _ k ( hk t ) ⟩,fun t=> hF.tip F _ t ( hv.path t ) ⟩ -- limit exponent coerces?
lemma status_plus (hF: Status F D)(hH: Status H U): Status (F+H) (D+U):= by
    obtain ⟨k,hK⟩:= hF.life; obtain ⟨h,hZ⟩:= hH.life; exact ⟨ ⟨ k+h,fun t=> ((hK t).up (by omega)|>.add ( (hZ t).up (by omega))) ⟩,fun t w=> ( hF.path t w ).add ( hH.path t w ) ⟩ -- derivative types.C.
lemma status_cast (h:Status F H) (c:ℂ): Status ( c • F ) ( c • H ):= ⟨ by obtain ⟨k,hK⟩:= h.life; exact ⟨k,fun i=> ( hK i ).smul _⟩, fun t w=> ( h.path t w ).const_mul c ⟩
lemma status_0 (A:Type): Status (0: OM A) 0:= ⟨ ⟨0,fun _ _ _=>rfl ⟩,fun _ _=>hasDerivAt_const ..⟩ -- projection
lemma status_sum {S:E→OM A}{U:E→OM A}(N:Finset E)(hx:∀ i∈N,Status (S i) (U i)): Status (∑ i∈N,S i) (∑ i∈N, U i):= by classical induction N using Finset.induction with| empty=> rw [Finset.sum_empty, Finset.sum_empty]; exact status_0 ..| insert i t hi ih=> rw [ Finset.sum_insert hi,Finset.sum_insert hi ]; exact status_plus (hx _ (by simp)) ( ih (fun j hj=>hx j (Finset.mem_insert_of_mem hj)))
-- for bulk, anchors
variable {n:Side}
lemma gl_Bulk (G:Gauge)(n:Side): Glance ( Bulk G n ):= by
    constructor; · intro F k h w hw; rw [bulkZ,point ]; split; rw [h _,mul_zero]; simpa [stage] using hw; rfl
    intro F H t hp w; by_cases hv:net w=0; · simp_rw [Function.comp_apply,bulkZ,if_pos hv, point]; exact ( hp (stage w) ).const_mul _
    simp_rw [Function.comp_apply, bulkZ, if_neg hv]; exact hasDerivAt_const ..
lemma gl_A (G:Gauge)(n:Side)(A:Cover): Glance (anchor G n A):= by
    constructor; · intro F k hp w hw; rw [ chase_now,point,hp _,mul_zero ]; simpa [stage] using hw
    exact fun F H t hp w=> ( hp (stage w) ).const_mul _
end YM.MS.Orbit
