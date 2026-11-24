import YM.SignedWilsonExpansion.Belfry.Clerk
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
open Generator Generator.Drive
-- strengthen overlap estimate to O(t^(q+1)), along arbitrary bounded paths.
-- probes quantify all of FieldEnd (attention to dual basis: no norm imported).
lemma salaryMul {x y:ι→FieldEnd G d} (v:S' (L:=L) x)(P:SeatsW.Salary ℂ L g y): SeatsW.Salary ℂ L g (fun i=>x i*y i):=by
     let b:= Module.finBasis ℂ (FieldEnd G d); intro a; have H(i):a (x i*y i)=∑ j,b.coord j (x i)*a ( b j*y i ):=by nth_rw 1 [← b.sum_repr (x i),Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_mul_assoc,map_smul]; rfl
     simp_rw [H]; apply IsBigO.sum; intro j _; exact ((v _).mul (P (a ∘ₗ LinearMap.mulLeft ℂ (b j)))).congr_right (fun i=>one_mul _)
lemma salaryShrink {x y z:ι→FieldEnd G d} (p:SeatsW.Discount ℂ L ε (x-y))(v: SeatsW.Salary ℂ L ε (y-z)): SeatsW.Salary ℂ L ε (x-z):= fun T=> (( ( p T ).isBigO.add ( v T ) ).congr_left fun i=> by change T (x i-y i)+T (y i-z i)=T (_-_); rw [←map_add]; exact congr_arg T (sub_add_sub_cancel (x i) (y i) (z i)) )
lemma sounded {p:ι→Cn} (v:funds L p): (fun i=> calcT (θ i) (q+1) (p i)-calcT (θ i) q (p i))=O[L] (θ^(q+1)):=by
    simp_rw[timed_step,add_sub_cancel_left]; exact ((v _).mul (( IsBigO.of_bound' ( f:=fun i=> (θ i:ℂ) ) ( g:=θ ) (Eventually.of_forall fun i=> (Complex.norm_real _).le) ).pow (q+1))).congr_right fun i => one_mul _
lemma stoppedY {F:ι→Guard G d}(v:Budget L F): SeatsW.Salary ℂ L (θ^(q+1)) (fun i=>young (q+1) (θ i) (F i)-young q (θ i) (F i)):=by intro a; simp_rw [_root_.map_sub a,yearParam]; exact sounded ( B_salary F a v )
variable {R:Initialize G}{K:Normalize.Store G}{V:Rose.Pick K}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}
variable (Q:Speed.Quoted R V Y S) (ν:ℝ) (h:G.Simple)
open Classroom GroupS Level Measure
local notation "Ω"=> gaugeN R V Y ν
local notation "Ω'"=> gaugeB V Y ν
local notation "Θ"=> GroupS.ψ V Y ν
include Q
lemma trimTick (p:FO L g)(x:(ε-Tone θ g Θ (q+1))=o[L](θ^(q+1))) : (ε-Tone θ g Θ q)=O[L](θ^(q+1)):=by
    let y0:(Tone θ g Θ (q+1)-Tone θ g Θ q)=O[L] (θ^(q+1)):=by
         obtain ⟨C,u⟩:= isBigO_iff.mp ( sounded (θ:=θ) (q:=q) ( eaten R V Q ν p ) ); refine IsBigO.of_bound C (?_); filter_upwards[u] with i hi; rw [Pi.sub_apply,←Complex.norm_real, Complex.ofReal_sub, show (Tone θ g Θ (q+1) i:ℂ)= _ from pure_tick ( b:=q+1 ) (permit R V Q ν (g i)) (θ i), show (Tone θ g Θ q i:ℂ)=_ from pure_tick ( b:=q ) (permit R V Q ν (g i)) (θ i) ]; exact hi
    exact (x.isBigO.add y0).congr_left fun i=> (sub_add_sub_cancel ..)
lemma trimPost {X:ι→ FieldEnd G d}(p:FO L g)(u:SeatsW.Discount ℂ L (θ^(q+1)) (fun i=> X i-Crisis.gate d (g i) (Classroom.Levy Ω θ g (q+1) i d))) : SeatsW.Salary ℂ L (θ^(q+1)) (fun i=> X i-Crisis.gate d (g i) ( Classroom.Levy Ω θ g q i d )):=by
    apply salaryShrink (x:=X) (z:=fun i=> Crisis.gate d (g i) ( Classroom.Levy Ω θ g q i d )) u
    intro a; apply IsBigO.congr_left (salaryMul (boundD p d) (stoppedY ( v:= checkedN R V Q ν p d ) (θ:=θ) ( q:=q )) a); intro i; exact congr_arg a (_root_.mul_sub ( Dial d (g i) ) _ _)
include h
lemma trimPre {X:ι→ FieldEnd G d}(p:FO L g)(u:SeatsW.Discount ℂ L (θ^(q+1)) (fun i=>X i-readyL ( V:=V ) (Y:=Y) ν θ g (q+1) i d)) : SeatsW.Salary ℂ L (θ^(q+1)) (fun i=>X i-readyL ( V:=V ) (Y:=Y) ν θ g q i d):=by
    apply salaryShrink (x:=X) (z:=fun i=> readyL ( V:=V ) (Y:=Y) ν θ g q i d) u; intro a; apply IsBigO.congr_left (salaryMul (boundD p d) (stoppedY ( v:= checked R V Q h ν p d ) (θ:=θ) (q:=q)) a); intro i; exact congr_arg a (_root_.mul_sub ( Dial d (g i) ) _ _)
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
