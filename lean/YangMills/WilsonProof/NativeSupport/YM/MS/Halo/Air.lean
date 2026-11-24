import YM.MS.Halo.Air
import YM.MS.Halo.Wind
/-!
# Rotations and prefix injections commute with local YM. Operations model
all finite continuation dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Alps
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {m n k:ℕ}{b:Bool}{z:ℂ}{X F H: Rack G n}{U Y:Mield G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
-- π.Morph.Surface.
structure Surf (G:Gauge)(m n:ℕ) where
    run: Rack G n→ₗ[ℂ] Rack G m
    profile: Arts.L m → Arts.L n→ ℂ
    fixC (c:ℂ) : run (coin c)=coin c
    prod (F H:Rack G n): run (bite n G F H) = bite m G (run F) (run H)
    vec (a:Arts.L n)(b:Bool) (i:G.ColorIndex): run (lip b (some a) i)=∑ j:Arts.L m, profile j a • lip b (some j) i
    noneC (b:Bool)(i:G.ColorIndex): run (lip (n:=n) b none i)=lip b none i
    drv (F:Rack G n)(a:Arts.L n): run (rowP a F)= ∑ i:Arts.L m, profile i a • rowP i (run F)
    iso (a b:Arts.L m): ∑ j:Arts.L n,profile a j*profile b j= if a=b then 1 else 0
namespace Surf
variable (P: Surf G m n) (K:Spin ( L n ))
-- fix distinguished insertion axes, no sum if used. b=false
abbrev keeps : Prop:= ∀ i:Axis, ∀ j:Arts.L m,P.profile j (chair n i)= if j=chair m i then 1 else 0
def orbit (K:Spin ( L n ))(G:Gauge) : Surf G n n where
   run:= (flagS K G).beam
   profile i j:= K.profile i j
   fixC:= vaultLeaf _
   prod:= circle_prod _
   vec a b i:= by
       unfold lip; ext s; rw [usesLeaf]; rcases s with _|⟨⟨⟨⟨_|j,h⟩,c⟩,p⟩,_|s⟩; -- ugly rcases splits Option before length
       all_goals simp only [ Finset.sum_apply, Pi.smul_apply,smul_eq_mul, Motif.leaf,note, mono]; simp [ flagS,leggo,rayS,Spin.prop,Spin.shadow,onX] <;> (by_cases he:c=i <;> by_cases hy:h=b <;> simp [he,hy]) -- unknown
   noneC b i:= by
       unfold lip; ext s; rw [usesLeaf]; rcases s with _|⟨⟨⟨⟨_|j,h⟩,c⟩,p⟩,_|s⟩ <;> first|rfl|simp [flagS,leggo,rayS,Spin.prop,Spin.shadow,onX, Motif.leaf,node1,mono] <;> (by_cases he:c=i <;> simp [he]) -- tine
   drv F a:= by
       ext l; let x:=net l; unfold rowP; simp_rw [beamMoon,Finset.sum_apply,Pi.smul_apply,moon,smul_eq_mul,spike_δ]; simp_rw [← mul_assoc, ← Finset.sum_mul]; -- values
       change Complex.I *( K.turn x a:ℂ)*_= _; congr 1; rw [← K.orth, Complex.ofReal_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; push_cast; unfold x; ring
   iso a b:= by obtain h:=K.weights a b; split <;> rename_i ht <;> first | ( simp only [ht,↓reduceIte] at *; exact_mod_cast h ) -- positive rewrites j?
lemma till (P:Surf G m n)(a:Axis)(hk:P.keeps){E:Type}[AddCommMonoid E][Module ℂ E](U:Arts.L m→E): ∑ j:Arts.L m, P.profile j (chair n a) • U j=U ( chair m a ):= by simp_rw [hk,ite_smul,zero_smul,one_smul]; simp
lemma orbit_s (h: K.within false): (orbit K G).keeps:= by
   intro i j; unfold orbit; dsimp only; rw [K.dual,Spin.profile]; rw [fixedBasis (Nat.zero_le n) ((K.within_back h) rfl)]; simp only [spray,Pi.single_apply]; split <;> simp_all
variable (h:m≤n)
def border (G:Gauge)(h:m≤n) : Surf G m n where
   run:={ toFun:= pulls h,map_smul':= fun _ _=>rfl,map_add':=fun _ _=>rfl }
   profile i j:= if rises h i=j then 1 else 0
   fixC i:= by funext l; cases l <;> rfl
   prod F H:= by
       ext l; change (product (field Landau.parity) F H) ( Arts.lift h l )=(product _ _ _) _; rw [scattered,scatter_up,scattered]; rfl
   vec a b i:= by
       rcases rangeA a h with ⟨j,rfl⟩|⟨j,rfl⟩
       · simp only [EmbeddingLike.apply_eq_iff_eq,ite_smul,zero_smul,one_smul]; simp; ext l; rcases l with _|⟨⟨⟨⟨_|k,a⟩,c⟩,p⟩,_|l⟩ <;> first| rfl| simp [lip,onX,Motif.leaf,node1,Arts.lift,pulls,embA]
       simp [ nowhere h _ j ]; ext l; rcases l with _|⟨⟨⟨⟨_|k,a⟩,c⟩,p⟩,_|l⟩ <;> first|rfl| simp [ lip,onX,Motif.leaf,node1,Arts.lift,pulls,embA,nowhere h _ j ]
   noneC b i:= by
       ext l; rcases l with _|⟨⟨⟨⟨_|k,a⟩,c⟩,p⟩,_|l⟩ <;> first|rfl| simp [ lip,onX,Motif.leaf,node1,Arts.lift,pulls,embA ]
   drv F a:= by
                       rcases rangeA a h with ⟨j,rfl⟩ | ⟨j,rfl⟩ <;> simp [ ite_smul,nowhere ]; · ext l; change moment _ F (Arts.lift h l)=_; rw [moon,rowP,moon, spike_δ,spike_δ, lifts_net]; simp only [spikeV,Left, lasts]
                       ext l; change moment _ F (Arts.lift h l)=0; rw [moon,spike_δ,lifts_net]; simp only [spikeV,Left,offt (rises h) _ _ (fun i=> nowhere h i j), Complex.ofReal_zero,mul_zero,zero_mul]
   iso a b:= by simp -- easy
lemma border_s (G:Gauge): (border G h).keeps:= fun i j=> by
   change (if rises h j=chair n i then (1:ℂ) else 0)=_; rw [ show chair n i=rises h ( chair m i ) from rfl]; simp only [EmbeddingLike.apply_eq_iff_eq]
end Surf
end YM.MS.Halo
