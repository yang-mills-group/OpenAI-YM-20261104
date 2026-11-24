import YM.MS.Mach.Plate
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Spray
/-!
# D rect lift, covariant derivative given insertion external axes.
No Bianchi or exact reduction during continuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {k m n:ℕ}{z:ℂ}{F H:Rack G n}{x y:ℝ→ Rack G n}{U Y:Mield G n}
local notation "Ψ"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product Ψ
local notation "Δ"=> forge ( Motif.dot (applyS z G n))
local notation "Ω"=> cwave n G
variable (i j:Axis)
namespace Pole
lemma cap (l:List Axis)(hz:star z=z) : Bay (Pole G n i j z l) (2+l.length) 0 (2+(l.length:ℤ)):= by
    induction l with
    | nil=> exact Bay.CurlB _ _ hz -- fix
    | cons a l ih=>
       simp only [Pole,List.length_cons,← add_assoc,Nat.cast_add,Nat.cast_one,convoke,LinearMap.add_apply,LinearMap.smul_apply];
       exact Bay.plus ((ih.axis (chair n a)).taller (by omega)) ((by simpa only [zero_add, add_comm 1,add_comm (1:ℤ)] using ((Bay.cov (chair n a)).Cartan ih).cash hz)) -- danger dims & Bool
lemma rank0 (l:List Axis)(a:G.ColorIndex): Book.rank 1 (Pole G n i j 0 l a):= by
    induction l with | nil=> simp only [Pole,cur,zero_smul,add_zero]; exact rank_α _ _ _|cons k l ih=> simp only [Pole,convoke,zero_smul,add_zero]; exact mon_apply ih _
-- µ marker spin. obtain Sturdy via Surf
lemma v_wall (l:List Axis)(A:Surf G m n)(h:A.keeps): A.air (Pole G n i j z l)=Pole G m i j z l:= by induction l with| nil=> rw [Pole, Pole,A.earth, A.till i h, A.till j h]| cons a l ih=> rw [Pole, Pole,A.grip,A.till a h, ih]
-- present.V global. parametrized to include colors for package construction.
-- Leading equality, Plaq.symbol $µ.N
lemma leading1 (b c:Axis)(k:G.ColorIndex): cur 0 (chair 0 b) (chair 0 c) k= Koszul.mono (( Plaq.mk b c []).mark k):= by
   simp only [cur, zero_smul,add_zero]; ext l; by_cases h:l.length=1; swap; · rw [rank_α _ _ _ _ (by rw [mod_int]; omega), grade1 _ _ (by rw [mod_int]; omega)]
   obtain ⟨⟨j,p⟩,rfl⟩:=List.length_eq_one_iff.mp h; rw [ c_α ]; rcases j with ⟨⟨_|j,_|_⟩,a⟩ <;> simp only [show chair 0 b=b from rfl,show chair 0 c=c from rfl]; all_goals by_cases hx:a=k <;> simp [at_g,Koszul.mono,Local.BV.gpath,Plaq.mark,der_nil, spikeV,hx] -- if j labels simp cross lifts
lemma markV (a:Axis)(d:Plaq) (k:G.ColorIndex) : rowP (chair 0 a) ( Koszul.mono (d.mark k) )= Koszul.mono (( Plaq.mk d.i d.j (a::d.jets)).mark k) := by
   ext l; rcases l with _|⟨⟨⟨⟨_|j,_|_⟩,c⟩,p⟩,_|s⟩ <;> simp only [rowP,moon, show chair 0 a=a from rfl]; all_goals simp [net, Koszul.mono,Plaq.mark,Local.BV.gpath,spike_δ,inc,spikeV,Lifting.der_add,mul_assoc]; -- `Net.h` 
lemma singleM (l:List Axis)(k:G.ColorIndex): Pole G 0 i j 0 l k= Koszul.mono ((Plaq.mk i j l).mark k):= by
    induction l with| nil=> exact leading1 ..| cons a l ih=> rw [Pole,convoke,zero_smul,add_zero,axisP,lock, ih]; exact markV a _ k
end Pole
end YM.MS.Mach
