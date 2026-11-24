import YM.MS.Breeze.Bulb
import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
/-! Price at each scale for gluing/Wick.S.Submodule -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Breeze
open Garment.Wick
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Puff Rake Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{F H:Law G}{t:ℝ}
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
local notation "K"=> (Job.single Unit)
local infix:70 " ⋄ "=> product (field Landau.parity)
variable (F H) {s:ℝ}
def dose (F H:Law G)(s:ℝ)(i j:BH G)(l r:Legs (Lane4 G))(p:QP) : ℂ:= (2:ℂ)⁻¹ * meshZ (PlanetD G s) i j F H l r p
local notation "P"=>PlanetD G s
lemma receipt (i j:BH G)(p:QP)(l r:Legs ( Lane4 G )): dose F H s i j l r p=(P i j p)*( sign Ψ (parity j) (D (i,p) F) l * D (j,-p) H r ):= by unfold dose meshZ; rw [at_sign,at_D, at_D ]; ring -- name
lemma receipt' (i j:BH G)(p:QP)(l r:Legs (Lane4 G)): dose F H s j i l r (-p)= P i j p * ( D (j,-p) (sign Ψ (parity i) F) l * D (i,p) H r ):= by
    rw [receipt,neg_neg, thRev s ]; -- kernelK j i? hp
    simp_rw [at_sign,at_D,at_sign,degree_cons]; change _=P i j p *((cross (parity i) ((parity j) ^^ degree Ψ l)*_) * _); rw [cross_right (parity i) (parity j),cross_comm (parity i) (parity j)]; ring -- need cross factor? receipt' uses Rp j i(-p) pref cross j i.Y.LHS sign after gives extra cross; RHS sign of D j of sign arg carries that exactly. abel
abbrev digest (F H:Law G)(s:ℝ)(i j:BH G)(p:QP)(l r:Legs (Lane4 G)):= dose F H s i j l r p + dose F H s j i l r (-p)
lemma entrance (i j:BH G)(p:QP)(w:Legs ( Lane4 G )) : P i j p* link (diffPair (i,p) (j,-p)) false Ψ F H w=scatter Ψ w (digest F H s i j p):= by
    have he : digest F H s i j p=fun l r=> P i j p • (sign Ψ (parity j) (D (i,p) F) l* D (j,-p) H r+D (j,-p) (sign Ψ (parity i) F) l * D ( i,p ) H r):= funext fun l=> funext fun r=> by rw [ digest, receipt, receipt', smul_eq_mul,mul_add];
    rw [he]; let Q:= allocate Ψ w ( R:=ℂ ); by_cases hp:P i j p=0; · rw [hp,zero_mul]; simp_rw [zero_smul]; exact (Q.map_zero)|>.symm
    rw [ link_pair (p:=Ψ) (i,p) (j,-p) ( thClosed s i j p hp ) F H,Pi.add_apply, scattered, scattered ]; rw [mul_add]; change (P i j p) • Q _+ (P i j p) • Q _=Q _; rw [← map_smul, ← map_smul, ← map_add ]; congr 1; ext1; rename_i u; ext1 v; exact ( mul_add (P i j p) _ _ )|>.symm
lemma Capitol (F H:Law G)(p:QP) : touchD G s p F H = (fun w=> scatter Ψ w (∑ i:BH G, ∑ j:BH G,digest F H s i j p ) ):= by
   funext w; change link _ _ _ _ _ _= _; unfold trc; simp_rw [ link_sum, link_scale, Finset.sum_apply,Pi.smul_apply ]; rw [ show scatter Ψ w (∑ i:BH G,_) =_ from map_sum ( allocate Ψ w ( R:=ℂ ) ) _ _ ]; simp_rw [ map_sum ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> entrance F H i j p w))
variable {F H}
lemma dosed (hp:F∈Wallet G)(hu:H∈Wallet G)(i j:BH G)(p q:Legs (Lane4 G)): Integrable (dose F H s i j p q) planeF:= by obtain he:= Wallet.hall hp hu s 0 i j p q; simp only [pay0,one_mul ] at he; exact he.const_mul _
lemma oriented (hp:F∈ Wallet G)(hu:H∈ Wallet G)(s:ℝ): linkD G s F H=Cabin 0 (PlanetD G s) planeF F H:= by
   funext w; let A(x:QP):=∑ i:BH G,∑ j:BH G,digest F H s i j x; have hg(a b: Legs (Lane4 G))(i j:BH G): Integrable (fun q=>digest F H s i j q a b) planeF:= ( dosed hp hu i j a b ).add ((dosed hp hu j i a b).comp_neg ) -- lemma
   have he (l r:Legs (Lane4 G)): Integrable (fun p=> A p l r ) planeF:= by simp_rw [ A,Finset.sum_apply ]; exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> hg l r i j))
   obtain h:= (scatter_integral planeF (f:=A) Ψ w (fun a b _=> he a b)).2; rw [( gateway hp hu s w ).2 ]; simp_rw [Capitol]; rw [h]; unfold Cabin; refine scatter_congr _ _ _ _ (fun a b he'=>?_); simp_rw [ pay0,one_mul ]; unfold A; simp_rw [Finset.sum_apply]; rw [ integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> hg a b i j)) ]; simp_rw [show ∀ i:BH G,(∫ p,∑ j:BH G,digest F H s i j p a b∂planeF) = _ from fun i=> integral_finsetSum _ (fun j _=> hg a b i j) ]; -- RHS meta inference under family maybe
   simp_rw [ digest, show ∀ i j:BH G,(∫ p,dose F H s i j a b p+dose F H s j i a b (-p)∂planeF)= (∫ p,dose F H s i j a b p∂planeF)+(∫ p,dose F H s j i a b p∂planeF) from fun i j=> by rw [integral_add ( dosed hp hu i j a b ) ( (dosed hp hu j i a b).comp_neg ),integral_neg_eq_self],dose, integral_const_mul, Finset.sum_add_distrib, ← Finset.mul_sum ]; nth_rw 2 [ Finset.sum_comm ]; ring -- nth_rw selector
end YM.MS.Breeze
