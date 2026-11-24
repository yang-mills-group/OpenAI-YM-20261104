import YM.FVA2.Smooth.Dialects
import YM.MS.Breeze.Seats
/-!
# Differentiate the formal continuum MS primitive joint kernels

Rewrite dynamics and boundary data on the `Rake` side in terms of unanchored
seats. Includes tag-support localization and preparing the recursion.
See `Smooth/Point`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
local notation "ℳ"=> (fun (_:I)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G I (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))

lemma mesh_t (i j:BH G)(x y:Legs (Lane4 G))(p:QP)(a b:QP)(F H:Law G)(P: Edge G): meshZ P i j ( chair G a F ) ( chair G b H ) x y p= Tone.bill a ( net x )*Tone.bill b ( net y )*(Tone.bill ( a-b ) p*meshZ P i j F H x y p):= by
    simp only [meshZ,seated,net_cons,Tone.rightadd,Tone.inverse,netπ]; ring
-- equality even off wallet, by commuting trivial phase outside integral
lemma ride_t (s t:QP) (F H:Law G)(P:Edge G): chair G t (Cabin ( s-t ) P planeF F H) = Cabin 0 P planeF (chair G s F) (chair G t H):= by
    symm; funext w; unfold Cabin; rw [seated]; let Q:= allocate Ψ w ( R:=ℂ ); change Q _= Tone.bill t (net w) • Q _; rw [← map_smul]; apply scatter_congr; intro x y he; simp_rw [Tone.pay0,one_mul,mesh_t,integral_const_mul, ← Finset.mul_sum ]; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul,← split_net he,Tone.rightadd, netπ ]; field_simp [ Tone.nonz ]
lemma traced (F:Law G)(x:QP)(s:ℝ)(q:QP)(w:Legs (Lane4 G)): trc (PlanetD G s) q (chair G x F) w= Tone.bill x (net w)*trc (PlanetD G s) q F w:= by
    simp_rw [ at_trc,seated,net_cons, ← add_assoc, add_neg_cancel,zero_add,mul_left_comm ( PlanetD G s _ _ _ ) (Tone.bill _ _),← Finset.mul_sum ]
variable [LinearOrder W] (x: Position W I)
def relax (p:I→QP): Glade G I →ₗ[ℂ] Glade G I where
  toFun A i k:= chair G ( p i ) ( A i k )
  map_add' _ _:= funext fun _=> funext fun _=> map_add (chair ..) ..
  map_smul' _ _:= funext fun _=> funext fun _=> map_smul ( chair .. ) ..
lemma cove (u: Glade G I)(p:I→QP)(i:I)(t:ℝ)(w:Legs (Lane4 G)): relax p u i t w=Tone.bill (p i) (net w)* u i t w:= rfl
lemma plate (F:Glade G I)(p:I→QP)(i:I)(k:ℝ)(w:Legs (Lane4 G)): ‖relax p F i k w‖ =‖F i k w‖:= by rw [ cove,norm_mul,Tone.bill_norm,one_mul ]
-- sells same price on absolute/pole integrands. fix syntax norm not spaces leading bug
abbrev perch (T:Finset W)(F:Glade G I): Glade G I:= relax (rootX x T) F
-- maybe conflicts `Plane.perch`; later use `shelf` name
lemma treeD (k:I→QP)(P:Planet G I)(F H:Glade G I): relax k ( expJ P F H )= expJ P F ( relax k H ):= by
   funext i t; exact Lifetime.commuteC (p:=Tone.bill (k i))|>.symm
lemma jump (k:I→QP)(F: Glade G I): relax k ( sailP ℳ Δ F ) = sailP ℳ Δ (relax k F):= by funext i t; exact (chairDeep ..).symm
lemma reorient (P:Planet G I) (T U: Finset W)(ht: U∈picks T)(X Z: Glade G I): perch x T ( regionC ℳ (rootX x U-rootX x T) P X Z )= regionC ℳ 0 P ( perch x U X ) ( perch x (T \ U) Z ):= by unfold perch; rw [unfT x ht]; funext i q; exact ride_t ..
-- chair of rootX T mark sector
abbrev aboard (X:Dance G I W): Dance G I W:= fun T k=> perch x T ( X T k )
abbrev road (x:Position W I)(F:Rake.Site G I)(X:Dance G I W) (s:Finset W)(k:ℕ):= Src x ℳ Δ Δ F X s k
lemma root_0 (s:Finset W) : rootX (0:Position W I) s=0:= by unfold rootX; split <;> rfl
lemma through (X:Dance G I W)(F:Rake.Site G I)(k:ℕ)(s:Finset W): perch x s (road x F X s k)= road 0 F (aboard x X) s k := by
   unfold perch road Src multi lonely; simp only [ map_add,map_sum, root_0,sub_zero ]; -- map non notation
   refine congr_arg₂ (·+·) ( Finset.sum_congr rfl fun i _=> treeD .. ) (Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j _=> reorient _ _ _ _ hi _ _ )
abbrev folk (X:Dance G I W)(s:Finset W)(k:ℕ)(F:Rake.Site G I):= sailP ℳ Δ ( X s k )+road x F X s k
lemma vouchers (X:Dance G I W)(F:Rake.Site G I)(k:ℕ)(s:Finset W): perch x s (folk x X s k F)=folk 0 (aboard x X) s k F:= by unfold perch folk; rw [map_add, jump]; exact congr_arg₂ (·+·) rfl (through ..); -- inspect rw
lemma riverT (k:I→QP)(F:Glade G I): relax k (river F) = river (relax k F) := by funext i t w; rw [cove]; unfold river; simp only [ cove ]; rw [ integral_const_mul ]
lemma motion {X:Dance G I W}{F:Rake.Site G I}{U:W→ Rake.Site G I}(hx: Fields x ℳ Δ Δ F U X)(k:ℕ){s:Finset W}(he:2≤s.card) : aboard x X s k= river (folk 0 (aboard x X) s k F):= by
    have hm: X s k=river (folk x X s k F):= (hx.2.2 s he k).2.2
    rw [← vouchers]; apply Eq.trans (congr_arg ( perch x s ) hm); exact riverT ..

variable (A:MS_Data G M) (p:W→Rake.Label b) (u v: Steps W) (V:Steps W→Dance G I W)
variable (P)
local notation "Ω"=> approach P A
local notation "χ"=> charted P A p
variable {P x}
lemma parity_mark {K L: Planet G I}{μ:I→Measure QP}{F:Rake.Site G I}{ U R: W→Site G I}{X Y:Dance G I W}(hf₁:Fields x μ K L F U X)(hf₂:Fields x μ K L F R Y)(s:Finset W)(hp:∀ i∈s,U i=R i): X s=Y s:= by
   induction s using Finset.strongInductionOn with| _ s ih=>
    rcases lt_or_ge s.card 2 with he|he
    · obtain hx|hx:= ( by omega: s.card=0 ∨ s.card=1 ); · rw [Finset.card_eq_zero.mp hx, hf₁.1,hf₂.1]
      obtain ⟨j,h⟩:= Finset.card_eq_one.mp hx; rw [h, hf₁.2.1, hf₂.2.1]; exact hp _ (by rw [h]; simp)
    funext k; induction k using Nat.strong_induction_on with
    | h k hK=>
      obtain H:= hf₂.2.2 s he k; suffices hp': multi μ x K L F (Y s) Y k s=multi μ x K L F (X s) X k s from Duty.consistent ( retire L μ ) ( hf₁.2.2 s he k ) (hp' ▸ H); unfold multi lonely; refine congr_arg₂ (· + ·) ( Finset.sum_congr rfl (fun i hi=>?_)) ( Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>?_ ); · rw [hK i (( mem_Ico.mp hi ).2)]
      obtain H:= n_small hi; rw [ ih i H.1 ( fun j hj=> hp j (H.1.le hj) ), ih _ H.2.2.2 ( fun j hj=> hp j ( H.2.2.2.le hj ) ) ]
lemma same (x: Position W I)(h:∀ i,charted P A p i x ( V i ))(T: Finset W)(k:ℕ)(i:I)(q:ℝ)(w:Legs (Lane4 G)): held v T (fun t=> aboard x ( V t ) T k i q w):= by
    intro t ht; obtain hv:∀ j∈T, hop v t j=v j:= fun j hj=> hop_other _ _ ( fun he=> ht ( mem_product.mpr ⟨ he,mem_univ _⟩ ) ) hj; have h0:= parity_mark ( h (hop v t) ) ( h v ) T ( fun i hi=> congr_arg (fun t=> beamH A P (p i) t) (hv i hi) ); change perch x T ( V (hop v t) T k ) i q w = perch x T ( V v T k ) i q w; rw [h0]
end YM.FVA2.Smooth.Cruise
