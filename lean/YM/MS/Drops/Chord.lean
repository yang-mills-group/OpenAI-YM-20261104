import YM.MS.Breeze.Seats
import YM.MS.Drops.Reeds
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
open Breeze Next.Rank Radian Flux
variable {s:ℝ}{f g:Local.BV.Grade G}{F H:Law G}{h k:ℤ}
local notation "L"=> PlanetD G s
local notation "α"=> Local.BV.Horizontal
lemma coin_s (t:ℂ)(a:QP): chair G a (coin t)=coin t:= by ext v; cases v with| nil=> rw [seated,show net ([]:Legs (Lane4 G))=0 from rfl,right0,one_mul]| cons p l=> exact mul_zero _
lemma hornDig (F:Local.BV.Grade G): Book.Limit ( Koszul.mono F ) 1:= by intro w he; rcases w with _| ⟨i,_|v⟩ <;> first| rfl | (simp at he)
abbrev singer (f:Local.BV.Grade G):= Koszul.mono f
lemma ticketK (c:QP)(ha:Horizontal f h)(hv:Horizontal g k): Cabin c L planeF (singer f) (singer g) = coin ( pair_slope f g c s ):= by
    let z(a b:BH G)(p:QP):= Tone.bill c p*(L a b p*f (a,p)*g (b,-p)); -- use c.bill invalid
    have hr (a b:BH G)(p:QP): Tone.bill c p* meshZ L a b (singer f) (singer g) [] [] p=2*z a b p:= by simp only [meshZ,degree_nil,cross_false',one_mul]; unfold z singer Koszul.mono; dsimp only; ring
    have hp:= Wallet.hall ( Wallet.faith ha ) ( Wallet.faith hv ) s c; have he (a b: BH G): Integrable (z a b) planeF:= by obtain ht:= hp a b [] []; simp_rw [hr a b] at ht; convert (ht.const_mul (2:ℂ)⁻¹) using 1; ext1; exact (inv_mul_cancel_left₀ (by norm_num) _).symm
    funext w; rcases w with _|⟨i,w⟩; swap; exact capjoin (hornDig _) (hornDig _) _ L c _ (by simp)
    unfold Cabin pair_slope; rw [scatter_nil]; simp_rw [ hr, show net ([]:Legs (Lane4 G))=0 from rfl,Tone.right0,one_mul,integral_const_mul ]; change ∑ _i:BH G,_=_; unfold coin; dsimp only; unfold Cdeg; simp_rw [ Finset.mul_sum ]; -- expands 2*? RHS.C.No mark. better refactor
    change _=2*(∫ p:QP,∑ a:BH G,∑ b:BH G,z a b p ∂planeF); simp_rw [ ← Finset.mul_sum ]; rw [integral_finsetSum _ (fun a _=> integrable_finsetSum _ (fun b _=> he a b)) ]; exact congr_arg ((2:ℂ)* · ) (Finset.sum_congr rfl fun a _=> ( integral_finsetSum _ (fun b _=> he a b) ).symm)
lemma smallK (a b:QP)(ha:Horizontal f h)(hv:Horizontal g k): linkD G s ( chair G a (singer f) ) ( chair G b (singer g) ) = coin ( pair_slope f g ( a-b ) s ):= by rw [ climb_c a b ( Wallet.faith ha ) ( Wallet.faith hv ), ticketK ( a-b ) ha hv, coin_s ]
end YM.MS.Drops
