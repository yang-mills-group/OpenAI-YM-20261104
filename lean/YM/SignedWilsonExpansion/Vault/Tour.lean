import YM.SignedWilsonExpansion.Camera.Void
/-! Purchase menu finite before precision, with a single authorization test per arity.
 Includes all full-replacement faces in SAME horizon; each basis substitution at
 own cap plus arbitrary fixed higher cap. Heat exposure on these stocks pays linear
 combinations rather than postulating fresh grants.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.SignedWilsonExpansion.Vault
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Homes Extra.FD
open Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries Purchases UVClock Schedules
open XSpace Commission Dancer Dancer.Drawing Dancer.Shell Dancer.Fort Dancer.Stitch Camera
open Asymptotics Precision XSpace.Normalize
open FVA2 FVA2.Dframe XSpace.Cirrus
open scoped Topology ContDiff Classical BigOperators ENNReal
variable {G:Gauge}{D n:ℕ}{a:Axis}{B:Plans a}
abbrev Slice (D:ℕ):Type:= {g: Fin (D+1)// 0< g.val}
abbrev Scarf (G:Gauge)(D:ℕ) := Bool × Σ g: Slice D, Option ( Toon G g.val )
abbrev SlotX (t:Scarf G D): Fin (D+1):= t.2.1
abbrev capD (b:Scarf G D):ℕ:= SlotX b
abbrev earD (b: Scarf G D) : Bool:= b.1
abbrev clothD (b:Scarf G D) : Sec G (capD b):= match b.2.2 with | none=> leaf _ _ | some x=> Logo G _ x
-- Fill with THIS cap unit. not substitute empty stencils.
abbrev cleanT (b:Scarf G D):Scarf G D:= ⟨b.1,b.2.1,none⟩
abbrev carryT (t:ℕ)(v:0<t)(p:t≤D)(y:Option ( Toon G t ))(e:Bool): Scarf G D:= ⟨e,⟨⟨t,Nat.lt_succ_of_le p⟩,v⟩,y⟩
lemma live (x:Scarf G D): 0<capD x∧ capD x≤ D:= ⟨x.2.1.2,Nat.le_of_lt_succ (SlotX x).isLt⟩
abbrev Draft (G: Gauge)(D:ℕ)(S:Plans a):= Σ (n:Fin (S.arity+2)), Fin (n.val+1) → Scarf G D
namespace Draft
variable (b:Draft G D B)
abbrev bill :ℕ:= b.1.val+1
abbrev port : Fin (bill b)→Scarf G D:= b.2
abbrev headR (p:0<D) (s:Bool): Scarf G D:= carryT 1 zero_lt_one p none s
abbrev first (p:0<D) (s:Bool): Draft G D B:= ⟨⟨0,by omega⟩,fun _=> headR p s⟩
abbrev arity (b:Draft G D B):ℕ:= b.1.val
lemma paid_n : B.hired (arity b) := b.1.isLt
abbrev cover (w : Finset (Fin (bill b))) : Draft G D B:= ⟨b.1,fun i=> if i∈w then port b i else cleanT ( port b i )⟩
end Draft
namespace Author
variable {ι:Type}{ℱ: Filter ι}{r:ι→ℝ}{C: Schedule}
lemma magnify (U: Pad n) : ∃ L:ℝ,0≤L∧ ∀ y∈ U.F,∀ i:Fin n,‖y i‖≤L:= by
    have he:IsCompact U.F:= U.roi.1; obtain ⟨R,-,hR⟩:=he.isBounded.subset_closedBall_lt (c:=0) 1; refine ⟨max 0 R,le_max_left ..,fun p q i=>(PiLp.norm_apply_le p i).trans ((show ‖p‖≤ R from by simpa only [Metric.mem_closedBall, dist_zero_right] using hR q).trans (le_max_right ..))⟩
structure CameraT (S:Plans a) where
   test : ∀ n: Fin (S.arity+2), Test (n.val+1)
   pad : ∀ n: Fin (S.arity+2), ℝ
   pos : ∀ n, 0<pad n
   real : ∀ n x, 0 ≤ (test n x).re
   vital : ∀ n x, x∈Metric.thickening (pad n) (S.m n).F → 0<(test n x).re
   U :ℝ
   broad : 0 ≤ U
   roomy : ∀ (n:Fin (S.arity+2)) (y: Points (n.val+1)), y ∈ (S.m n).F → ∀ i:Fin (n.val+1), ‖y i‖ ≤ U
lemma paidCamera (S: Plans a): Nonempty (CameraT S):=by
   choose f ε h hU hp using ( fun n:Fin (S.arity+2)=> Integration.Cope.available ( S.m n ).roi.1 ( S.m n ).roi.2 )
   choose L hL l using (fun n:Fin ( S.arity+2 )=> magnify (S.m n)); refine ⟨ f,ε,h,hU,hp,∑n,L n,Finset.sum_nonneg (fun i _=> hL i),fun i p hi a=> ( l i p hi a ).trans (Finset.single_le_sum (f:=L) (fun n _=> hL n) (Finset.mem_univ i))⟩
variable (P: CameraT B) (f:ι→ℕ)(hr:Tendsto r ℱ trail)(p:Tendsto (sizeP r f C) ℱ (𝓝 0))
variable (b:Draft G D B) (z:ι→ Fin (Draft.bill b)→ Cover) (w: pad0 (B.m b.1) r f z ℱ C)
include hr w P p
lemma stampPoint : ∀ᶠ i in ℱ, (∀ R:Side, Integration.WilsonAddressedPhysicalCells.mass (P.test b.1) (C.a (f i)) (r i) R (wrap R∘ z i)≠0) ∧ (∀ v,‖C.gridPoint ( f i ) (z i v)‖≤ P.U*r i):=by
     let Z:ℝ:=4*(Draft.bill b); have hv:= (p.const_mul Z).eventually_lt_const ( by rw [mul_zero]; exact P.pos b.1 ); filter_upwards [hv, hr.eventually self_mem_nhdsWithin,w ] with i h' hi w'; refine ⟨ fun x=> Integration.Cope.actor (P.test b.1) (P.pad b.1) (P.pos _) (P.real b.1) ( P.vital b.1 ) ( z i ) ( show 0 < r i from hi ) (C.a_pos _) x h' w',fun t=>?_ ⟩
     rw [ congr_fun ( Integration.Cope.allowance (z i) 0 ( f i ) C ( show 0<r i from hi ) ) t,norm_smul, Real.norm_of_nonneg (show 0<r i from hi).le,mul_comm P.U ]; exact mul_le_mul_of_nonneg_left (P.roomy b.1 _ w' t) ( show 0<r i from hi ).le
end Author
end YM.SignedWilsonExpansion.Vault
