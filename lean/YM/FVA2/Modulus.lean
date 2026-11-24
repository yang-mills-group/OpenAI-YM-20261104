import YM.FVA2.NewTime
/-!
# The log-algebra of multi-fields. Use μ interpolation, not interchanging asymptotic
expansions in arbitrary matrix-erased schemes. Need linearity across fields at DIFFERENT
values of μ, since `Cabin` and `sail` and disk-edge limits don't define full linear
maps on unstable inputs.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 920000
namespace YM
namespace MS
namespace FV2Mod
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City Dock Emit Mach Land Pearl Train Menus Hem Mell
open Puff Engine SplitP Actors -- may conflict stage.Quotify prefix.
open Logarithm
open scoped Topology ContDiff Interval
variable {I W J S:Type} {G:Gauge}
section operators
open Koszul ( scatter ) -- not needed
local notation "Ψ"=> field ( Landau.parity ( A:=Axis ) (C:=G.ColorIndex))
variable {K:Edge G}{μ:Measure QP}{F H:I→Law G}{P:Law G}{A:QP}
lemma scatterWealth (w:Legs (Lane4 G))(u:I→Shared (Lane4 G) ℂ)(T:Finset I) : scatter Ψ w (fun i j=>∑ k∈T,u k i j)=∑ k∈T,scatter Ψ w (u k):= by simp_rw [← Finset.sum_apply]; exact map_sum (allocate Ψ w) ..
lemma scatterSm (w:Legs (Lane4 G))(u: Shared ( Lane4 G) ℂ)(t:ℂ): scatter Ψ w (fun i j=> t * u i j) = t • scatter Ψ w u:= map_smul ( allocate Ψ w ) ..
abbrev Hut (t:I→ℂ)(S:Finset I) (f:I→Law G): Law G:= ∑ i∈S,t i • f i
private lemma sc_coil (S:Finset I)(t:I→ℂ)(hv:∀ i∈S,SatP μ K P (H i) A): Cabin A K μ P ( ∑ i∈S, t i • H i )=∑ i∈S,t i • Cabin A K μ P (H i):= by
   funext w; unfold Cabin; let z(i j:BH G)(a b:Legs (Lane4 G))(k:I)(p:QP):= Tone.bill A p * meshZ K i j P ( H k ) a b p; have hm(i j:BH G)(a b:Legs (Lane4 G))(p:QP): Tone.bill A p*meshZ K i j P ( Hut t S H ) a b p=∑ k∈S,t k*z i j a b k p:= by
       unfold z meshZ Hut; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun k hk=>?_ ; ring
   have he(a b:Legs (Lane4 G))(i j:BH G): (∫ p,Tone.bill A p*meshZ K i j P (Hut t S H) a b p∂μ)=∑ k∈ S,t k * ∫ p,z i j a b k p ∂μ:= by
        simp_rw [hm]; rw [MeasureTheory.integral_finsetSum _ (fun k hk=> Integrable.const_mul (show Integrable _ μ from hv k hk i j a b) _)]; simp_rw [integral_const_mul]; rfl
   -- A compact reorganization. Avoid simplifying all.
   unfold Hut at he; simp_rw [ he, Finset.sum_comm (t:=S) (s:=(Finset.univ:Finset (BH G))), ← Finset.mul_sum _ _ (t _) , Finset.mul_sum (s:=S), mul_left_comm ( Tone.bill A ( net _ ) ) ( t _ ) , scatterWealth ];
   simp_rw [Finset.sum_apply,Pi.smul_apply]; exact Finset.sum_congr rfl fun k hk=> scatterSm w _ _
private lemma co_sc (S:Finset I)(t:I→ℂ)(hv:∀ i∈S,SatP μ K (F i) P A): Cabin A K μ ( ∑ i∈S, t i • F i ) P= ∑ i∈S,t i • Cabin A K μ ( F i ) P:= by
   funext w; unfold Cabin; let z(i j:BH G)(a b:Legs (Lane4 G))(k:I)(p:QP):= Tone.bill A p * meshZ K i j ( F k ) P a b p; have hm(i j:BH G)(a b:Legs (Lane4 G))(p:QP): Tone.bill A p*meshZ K i j ( Hut t S F ) P a b p=∑ k∈S,t k*z i j a b k p:= by
       unfold z meshZ Hut; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum, Finset.sum_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun k hk=>?_ ; ring
   have he(a b:Legs (Lane4 G))(i j:BH G): (∫ p,Tone.bill A p*meshZ K i j ( Hut t S F ) P a b p∂μ)=∑ k∈ S,t k * ∫ p,z i j a b k p ∂μ:= by
        simp_rw [hm]; rw [MeasureTheory.integral_finsetSum _ (fun k hk=> Integrable.const_mul (show Integrable _ μ from hv k hk i j a b) _)]; simp_rw [integral_const_mul]; rfl
   -- A compact reorganization. Avoid simplifying all.
   unfold Hut at he; simp_rw [ he, Finset.sum_comm (t:=S) (s:=(Finset.univ:Finset (BH G))), ← Finset.mul_sum _ _ (t _) , Finset.mul_sum (s:=S), mul_left_comm ( Tone.bill A ( net _ ) ) ( t _ ) , scatterWealth ];
   simp_rw [Finset.sum_apply,Pi.smul_apply]; exact Finset.sum_congr rfl fun k hk=> scatterSm w _ _
local notation "D"=> constantP G Unit (PlanetD G)
local notation "m0"=> (fun (_:Unit)=>planeF)
variable {F H:I→ Glade G Unit}{A:Glade G Unit} (T:Finset I)(t:I→ℝ)
lemma sl (F:Glade G J)(t:ℝ): (t:ℂ) • F=t • F:= by funext i u v; simp [Complex.real_smul]
lemma region_right (p:QP) (ht: Warm A false)(hp:∀ i∈T,Warm (H i) false): regionC m0 (fun _=>p) D A (∑ i∈T,t i • H i)=∑ i∈T,t i • regionC m0 (fun _=>p) D A ( H i ):= by
    simp_rw [← sl ]; funext i s; unfold regionC; simp_rw [Finset.sum_apply,Pi.smul_apply ]; exact sc_coil T (fun i=>(t i:ℂ)) ( H:=fun x=>H x i s) (fun j hj=> parkD.room (μ:=(fun _=>planeF)) (K:=D) (z:=fun _=>p) (hp j hj) ht (Upcoming Unit G) (fun _=>Coherent) i s)
lemma region_left (p:QP) (ht: Warm A false)(hp:∀ i∈T,Warm (H i) false) : regionC m0 (fun _=>p) D (∑ i∈T,t i • H i) A=∑ i∈T,t i • regionC m0 (fun _=>p) D ( H i ) A:= by
    simp_rw [← sl ]; funext i s; unfold regionC; simp_rw [Finset.sum_apply,Pi.smul_apply ]; exact co_sc T (fun i=>(t i:ℂ)) ( F:=fun x=>H x i s) (fun j hj=> parkD.room (μ:=(fun _=>planeF)) (K:=D) (z:=fun _=>p) ht (hp j hj) (Upcoming Unit G) (fun _=>Coherent) i s)
lemma sail_linear (hp:∀ i∈T,Warm (H i) false): sailP m0 D (∑ i∈T,t i • H i)=∑ i∈T,t i • sailP m0 D ( H i ):= by
    simp_rw [← sl ]; funext i s v; unfold sailP cycle; simp_rw [Finset.sum_apply,Pi.smul_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integral_finsetSum _ (fun j hj=> Integrable.const_mul ( Sat_W (m:= (fun (_:Unit)=>planeF)) (L:=(constantP G Unit (PlanetD G))) (hp j hj) ( masterD G Unit ( Tide.frameF Unit 0 ) ).pool ( fun _=>Coherent ) i s v (fun q=>Bool.noConfusion q)) _ ), integral_const_mul ]; -- check simp args
lemma trip_sum (hp: ∀ i∈T,Warm ( F i ) false)(hv:∀ i∈T,Trip (sailP m0 D) ( F i ) ( H i )): Trip (sailP m0 D) (∑ i∈T,t i • F i) (∑ i∈T,t i • H i):= by
    let S:=( sailP m0 D ); let Q(i):= S ( F i )+H i; have He(i:Unit)(v:ℝ)(w:Legs (Lane4 G))(j:I)(hj:j∈T): IntegrableOn (fun t:ℝ=>Q j i t w) (Set.Iic v):= (hv j hj).2.1 _ _ _ (fun h=> Bool.noConfusion h);
    unfold Trip; rw [ sail_linear T t hp, ← Finset.sum_add_distrib ]; simp_rw [← smul_add ]; refine ⟨ collected T (fun i hi=> ?_), ?_,?_⟩;
    · obtain ⟨k,hk⟩:= (hv i hi).1; refine ⟨ k, fun i u w hw=> ?_ ⟩; simp only [Pi.smul_apply,hk i u w hw, smul_zero ]; -- i shadow
    · intro i v w hc; simp_rw [ Finset.sum_apply,Pi.smul_apply ]; exact integrable_finsetSum _ fun j hj=> Integrable.smul _ ( He i v w j hj ) -- fix
    funext i v w; have hm (K:Glade G Unit): river K i v w=∫ t in Set.Iic v,K i t w:= rfl; rw [hm]; simp_rw [ Finset.sum_apply,Pi.smul_apply]; rw [integral_finsetSum _ (fun j hj=> show Integrable (fun u:ℝ=> t j • Q j i u w) (volume.restrict (Set.Iic v)) from Integrable.smul ( t j ) (He i v w j hj))]; simp_rw [MeasureTheory.integral_smul]; exact Finset.sum_congr rfl fun j hj=> congr_arg (fun u:Glade G Unit=> t j • u i v w) ((hv j hj).2.2)
-- expJ.Pair linearizable
local notation "Ω" => Glade G Unit
private def Web : (I→Ω) →ₗ[ℝ] ( I→Ω )→ₗ[ℝ] I→ Ω where
   toFun F:= {
      toFun:= fun H i=> expJ D ( F i ) ( H i )
      map_add' x y:= funext fun i=> funext fun t=> funext fun s=> map_add (boulevard Landau.parity ( D t s ) ( F i t s )) _ _
      map_smul' x y:= funext fun i=> by dsimp only [Pi.smul_apply, RingHom.id_apply]; simp_rw [ ← sl ]; exact funext (fun t=>funext (fun s=> map_smul (boulevard Landau.parity ( D t s ) ( F i t s )) _ (y i t s))) }
   map_add' F H:= LinearMap.ext fun A=> funext fun i=> funext fun t=> funext fun s=> map_add (LinearMap.flip (boulevard Landau.parity ( D t s )) ( A i t s )) _ _
   map_smul' x F:= LinearMap.ext fun A=> funext fun i=> by change expJ D ( x • F i ) _= x • expJ _ _ _; simp_rw [ ← sl ]; exact funext (fun t=>funext (fun s=> map_smul (LinearMap.flip (boulevard Landau.parity ( D t s )) ( A i t s )) _ (F i t s)))
lemma tube (F H:ℝ→I→Glade G Unit)(hf:Ready F) (hp:Ready H): Ready (fun v:ℝ=> fun i=> expJ D ( F v i ) ( H v i )):= hf.pair Web hp
end operators
end FV2Mod
end MS
end YM
