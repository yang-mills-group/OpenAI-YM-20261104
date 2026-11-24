import YM.MS.Motif.Alpha
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Receipt
/-!
# Master equation yields Council.System.Bulk and Trill test by all-order identity
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native Book Convolve Signal Dock Emit Rock Path Oceans
open Literal Hem Mell
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ}{z:ℂ}{F H:Mield G n}{U P: Box (Mob G)}
local notation "S"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
lemma blaze_sym (z:ℂ)(i:Chan G n): Symm S ( applyS z G n i ):= by
   have hA(a:Arts.L n)(i:G.ColorIndex): Symm S ( A n G a i ) := note_sym ( at_g a i ) (fun _:SectorP n=>(1:ℂ)); have hg(i:G.ColorIndex): Symm S ( cwave n G i ) := note_sym (onX (G:=G) false (none,i)) (fun _:SectorP n=>1)
   rcases i with ⟨_|i,a⟩; exact (vect_sym a hg hg).smul _; change Symm S (convoke z i (cwave n G) a); unfold convoke; rw [LinearMap.add_apply,Pi.add_apply]; exact (m_sp ( hg a ) _).add ( (vect_sym a ( hA i ) hg).smul _ )
lemma erupt (G:Gauge)(z:ℂ): Rock.sym (ploy G z) := fun n=> by
   unfold ploy core; refine ( Symm.smul _ ( Symm.sum _ (fun a _=> Symm.sum _ fun b _=>Symm.sum _ fun i _=> ?_) )).add ?_; exact ( Cur_sym a b z i ).times ( Cur_sym a b z i ); exact Symm.sum _ fun i _=> Symm.smul _ (Symm.times ( note_sym ( onX true i) (fun _:SectorP n=> (1:ℂ))) (blaze_sym z i))
-- interpret.Y.Lift.Prec formula Eval coefficient. 
abbrev Eigen (c:ℂ)(X F:Box (Mob G)):= Boom 0 (sweepQ ( Wick.Q G )) F+c • root ( squad ( Wick.D0 G )) X F -- parenth `→+...` parse
lemma reserved (c:ℂ)(X F:Box ( Mob G))(i:ℕ): linear (Mob G) (Eigen c X F) i=BasisC (linear (Mob G) X) ( linear (Mob G) F) c i := by rw [Eigen,BasisC,map_add,map_smul,Pi.add_apply,Pi.smul_apply,Literal.whole,pair_real]; rfl
lemma reserve (X F:Box ( Mob G))(c z:ℂ): value ( Mob G ) z (Eigen c X F) = sweepQ ( Wick.Q G ) (value ( Mob G ) z F)+ c • squad ( Wick.D0 G ) (value ( Mob G) z X) ( value ( Mob G ) z F):= by rw [Eigen,map_add,linear_v,map_smul,pair_v]
local notation "Ω"=> χ G
private lemma projectC (B:Mob G)(X:Mob G)(hX:Rock.sym X)(hp:tide X)(ht: Equal true ( squad ( Wick.D0 G) ( X + B ) (X+B)) 0)(hb: B=ploy G 0) : Equal true ( sweepQ ( Wick.Q G ) X+ ( (2:ℂ)⁻¹ ) • squad ( Wick.D0 G ) X X) 0:= by
    subst B; let Z:=ploy G 0; let U := squad ( Wick.D0 G ); have hB(n): Pure (field parity) false (Z n):= ploy_p 0; have hh(n): closed ( Wick.D0 G n) parity true := City.closure _ (City.laplace_cl _); intro n w hw; have he:=ht n w hw; have hw:=hw rfl;
    have hu : U X Z n w=U Z X n w:= axis_comm (hh _) (hp _) ( hB n ) hw;
    have hv : U Z Z n w=0:= AllMaster 0 hw; have hv' : U Z X=sweepQ ( Wick.Q G) X:= funext fun i=> φQ (hX i); change U (X+Z) ( X+Z ) n w=0 at he; simp only [ map_add, LinearMap.add_apply,Pi.add_apply,hu,hv,hv'] at he;
    change sweepQ ( Wick.Q G ) X n w+(2:ℂ)⁻¹* (U X X n w)= 0; linear_combination (1/2:ℂ) * he
lemma wisdom : Council (pulseX G) := by
    let x:= χ G; let b:ℂ:= (2:ℂ)⁻¹; let U:= Eigen b x x; have hp(z:ℂ): Equal true (value ( Mob G ) z U) 0:= by unfold U; rw [reserve]; let F:= value ( Mob G ) z x; have he: F = ploy G z-ploy G 0:= Class_at G z; apply projectC (ploy G 0) F _ _ _ rfl; exact he ▸ (fun i=> (erupt G z i).sub (erupt G 0 i)); exact he ▸ (fun i=> by simpa only [neg_one_smul, ← sub_eq_add_neg,Pi.sub_apply] using (ploy_p z (n:=i) (G:=G)).add ((ploy_p (G:=G) 0).smul (-1:ℂ))); rw [he,sub_add_cancel]; exact fun i l hl=> AllMaster z (hl rfl)
    intro n m l hl; unfold pulseX; rw [← reserved]; exact valuedZ U ( Garment.Wave.slice l ) (fun i=> hp i m l hl ) n
-- Operator action test from point Ward basis.Need all clocks mark gauge.
lemma judgment {X:Box ( Mob G)}(H:∀ z:ℂ, Rock.sym (value ( Mob G ) z X))(ht:∀ z:ℂ, squad ( Wick.D0 G ) (ploy G z) ( value ( Mob G ) z X )= 0): Trill (pulseX G) (linear _ X) := by
   have he (z:ℂ) : value ( Mob G ) z (Eigen 1 (χ G) X) = 0 := by rw [ reserve,one_smul, Class_at,map_sub, LinearMap.sub_apply,ht,zero_sub, show squad ( Wick.D0 G ) (ploy G 0) ( value ( Mob G) z X )= sweepQ _ _ from funext (fun i=> φQ (H z i)),add_neg_cancel]
   intro n m l hl; rw [show BasisC _ _ _ n= _ from (reserved 1 (χ G) X n).symm]; exact valuedZ _ (Garment.Wave.slice l) ( fun x=> congr_fun (congr_fun (he x) m) l ) n
end YM.MS.Motif
