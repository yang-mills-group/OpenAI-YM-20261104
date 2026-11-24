import YM.MS.Vane.Trigger
import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
/-! Price at each scale for gluing/Wick.S.Submodule -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Breeze
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Puff Rake Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{F H:Law G}{t:ℝ}
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
local notation "K"=> (Job.single Unit)
local infix:70 " ⋄ "=> product (field Landau.parity)
def Wallet (G:Gauge): Submodule ℂ ( Law G ) where
    carrier:= setOf (fun X=> Lease false false K (fun _=>X) 1 )
    zero_mem':= Lease.zero (fun _=>zero_le_one)
    add_mem':= Lease.plus
    smul_mem' c _ h:= Lease.cash c h
lemma permits : F∈Wallet G↔ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ x:Wire (BH G) E QP, Bound K (fun (_:Unit)=> fieldVal F x) 1:= by
    constructor <;> intro h; · intro E _ _ w; obtain he:= h E w (fun p=> Bool.noConfusion p) (fun p=> Bool.noConfusion p); simp only [Cape,cw,Pi.one_apply,one_zpow,mul_one] at he; exact he
    intro E _ _ w hx hp; unfold Cape; simp only [ cw,one_zpow,Pi.one_apply,mul_one ]; exact h E w
lemma Wallet.awake {U: Glade G I} (hF:Warm U false)(i:I)(t:ℝ) : U i t∈ Wallet G:= permits.mpr (fun E _ _ w=>comfort hF i t w (fun i=>Bool.noConfusion i))
lemma Wallet.product (hf:F∈ Wallet G)(hH:H∈ Wallet G): F ⋄ H∈ Wallet G:= by
    apply permits.mpr; intro E _ _ w; unfold fieldVal; simp_rw [scattered,sail_scatter ]; refine gather_bound w fun a b _=> ?_; convert! ( permits.mp hf E a ).mul ( permits.mp hH E b ) using 1; ext; simp -- price.
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma spaceArc : K = Arc.path (0:Arc.UScale Unit):= by unfold Arc.path Job.single; congr! 1; ext; simp
lemma Breath (f:ℝ)(x:ℝ) : True:= trivial -- remove
lemma existent (Z:E): Bound K (fun (_:Unit) (_:E)=> ( (Z) )) 1:= by rw [ spaceArc ]; exact Rock.at_rate ( Rock.Path.const_sc .. )
lemma blankB (c:ℂ): Bound K (fun (_:Unit) (_:E)=> c) 1:= by rw [spaceArc]; exact Rock.at_rate ( Rock.Path.const_sc .. )
lemma Wallet.cash : (coin (1:ℂ)) ∈ Wallet G:= permits.mpr (fun E _ _ w=> by rcases w with _|_; exacts [blankB (1:ℂ),blankB (0:ℂ)] )
lemma Wallet.faith {f:Local.BV.Grade G}{h:ℤ}(ht:Local.BV.Horizontal f h): (mono f)∈ Wallet G:= by
    apply permits.mpr; intro E _ _ w; rcases w with _| ⟨i,_|l⟩; exact blankB (0:ℂ); swap; exact blankB (0:ℂ)
    let F:E→ℂ:=fun t=>f (i.1,i.2 t); change Bound K ( fun _=>F ) _; have he := Plane.Shape.linear ((Local.seedStar.mp ht.1).form i.1) i.2; change Shape F _ at he
    have h (p:ℤ)(H:Shape F p): Bound K (fun (_:Unit)=> F) 1:= by rcases lt_or_ge p 0 with he|he; · rw [ H.charge he ]; exact blankB (0:ℂ)
                                                                 lift p to ℕ using he; rw [H.form,spaceArc]; exact Hem.consPrice (g:=fun (_:Unit) (_:E)=> Tensor.coeff F p 0) (Rock.at_rate ( Rock.Path.const_sc .. ))
    exact h _ he
lemma SheetU (s:ℝ): Sheet K 1 (fun _=> PlanetD G s):= by
    intro i j; let x:=‖s‖+1; let Z:= PlanetD G s i j; 
    have he:= Rake.transport ( a:=fun (_:Unit)=>s ) (star_r i j) (fun i=>le_refl (‖s‖)) ( norm_nonneg s ) (n:= (4:ℤ)-wfield i-wfield j); simp only [cw,one_zpow, Pi.one_apply, mul_one]; rw [planetEra _ _ s]; exact he -- planetEra under ∀? need simp
lemma Wallet.cour (h:F∈Wallet G)(s:ℝ) : Pass (PlanetD G s) F planeF:= by obtain ⟨d,hD,hW⟩:= funds Unit Coherent; exact fun l=> herec hW (SheetU s) (Lease.highp (show Lease false false K _ _ from h)) (fun _=>zero_le_one) (fun _=>zero_le_one) () l (fun i=>Bool.noConfusion i)
lemma Wallet.hall (h:F∈ Wallet G)(ht:H∈ Wallet G)(s:ℝ)(x:QP) : SatP planeF (PlanetD G s) F H x:= by obtain ⟨d,hD,hW⟩:= funds Unit Coherent; exact priceP ( SheetU s ) ( Lease.highp ( show Lease _ _ _ _ _ from h ) ) ( Lease.highp ( show Lease _ _ _ _ _ from ht ) ) hW () x
lemma Wallet.skyC (hp:F∈ Wallet G)(s:ℝ): cycle ( PlanetD G s ) planeF F ∈ Wallet G:= by
    obtain ⟨d,hD,hW⟩:= funds Unit Coherent; obtain hu:= planC (Lease.highp ( show Lease false false K (fun _=>F) 1 from hp)) (SheetU ( G:=G ) s) hW hD (fun _=>zero_le_one) (fun _=>zero_le_one); rw [one_mul] at hu; exact hu
end YM.MS.Breeze
