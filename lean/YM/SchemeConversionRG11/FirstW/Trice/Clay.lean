import YM.SchemeConversionRG11.FirstW.Trice.Blender
import YM.Pert.Triangle.FirstChange
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open MvPolynomial
open scoped Topology ContDiff BigOperators Matrix Classical
variable {T:Itinerary}{G:Gauge}{p:Nodes}{F:Labels.Frames G}
def seaU (G:Gauge): Deck.Part G 6:= (2:ℂ)⁻¹ • ∑ b:Badge G, (Glyph b false* Glyph b false)
def tau (x y z:Badge G):ℂ:= (eps3 x.1 y.1 z.1:ℂ)*(colorF x.2 y.2 z.2:ℂ)
def orbZ (G:Gauge): Deck.Part G 6:= ∑ i:Badge G,∑ j:Badge G,∑ k:Badge G,tau i j k • (Glyph i true * Glyph j true * Glyph k true)
lemma tau_spin (x y z:Badge G):tau y z x=tau x y z:= by unfold tau; rw [color_rotate y.2 z.2 x.2,show eps3 y.1 z.1 x.1=eps3 x.1 y.1 z.1 from by rw [eps_swap23,eps_swap12,neg_neg] ]
lemma tau_flip (x y z:Badge G): tau x z y=tau x y z:=by unfold tau; rw [color_second x.2 z.2 y.2, eps_swap23 x.1]; push_cast;ring
lemma sea_un : uncap (seaU G) = uMinus G:= by unfold seaU uncap; rw [map_smul,map_sum]; simp only [map_pow,← sq,show ∀ x:Badge G,MvPolynomial.rename Subtype.val (Glyph x false)=fanLeg false x.1 x.2 from fun x=>proved x false];unfold uMinus;rw [Fintype.sum_prod_type]; rw [smul_eq_C_mul]
lemma orb_un : uncap (orbZ G)= bFan G:= by
 have hv(i j k:Badge G): uncap (tau i j k • (Glyph i true * Glyph j true*Glyph k true))=triple (i.1,j.1,k.1) (i.2,j.2,k.2):= by
    rw [triple, smul_eq_C_mul];unfold tau uncap; simp only [map_mul,rename_C]; apply congrArg _; exact congrArg₂ (·*·) (congrArg₂ (·*·) (proved i true) (proved j true)) (proved k true)
 unfold orbZ uncap; simp_rw [map_sum,show ∀ i j k:Badge G, rename Subtype.val (tau i j k • (Glyph i true * Glyph j true * Glyph k true))= _ from hv]; simp_rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
 conv_lhs=> arg 2; intro a; rw [Finset.sum_comm]; -- ordering k after
 rw [Finset.sum_comm]
lemma seaC (F:Labels.Frames G)(i:P) (he:i≠0): cloak F (basic F i)= seaU G:= by apply rename_injective Subtype.val Subtype.val_injective; change uncap _=uncap _;rw [sea_un,stretch,bare_own, Triangle.triad, if_neg he]
lemma orbC (F:Labels.Frames G): cloak F (basic F 0)=orbZ G:= by apply rename_injective Subtype.val Subtype.val_injective;change uncap _=uncap _;rw [orb_un,stretch,bare_own,Triangle.triad,if_pos rfl]
abbrev ct (b:Badge G)(u:Bool)(i:Who G 6):ℂ:=↑(token b u i)
lemma primg (b:Badge G)(u:Bool)(f:Deck.Part G 6)(a:Who G 6): D1 a (Glyph b u*f)=(ct b u a) • f+Glyph b u*D1 a f:= by unfold D1; rw [pderiv_mul,show pderiv a (Glyph b u)=_ from count_glyph ..,C_mul']
lemma sea_one (a:Who G 6): D1 a (seaU G)=∑ b:Badge G,(ct b false a) • Glyph b false := by
 simp_rw [seaU, D1,Derivation.map_smul, map_sum]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro b _; change (2:ℂ)⁻¹ • D1 a (Glyph b false*Glyph b false)=_; rw [primg, count_glyph, mul_comm (Glyph b _),C_mul', ←two_smul ℂ]; rw [inv_smul_smul₀ (by norm_num)]
lemma sea_twice (a b:Who G 6): D1 a (D1 b (seaU G))=∑ x:Badge G,(ct x false b*ct x false a) • (1:Deck.Part G 6):=by
 rw [sea_one]; unfold D1; rw [map_sum]; apply Finset.sum_congr rfl; intro s _; rw [Derivation.map_smul, show pderiv a (Glyph s false) =_ from count_glyph s false a]; rw [mul_smul]; simp [smul_eq_C_mul]
lemma cyc (V:Type*)(w:Finset V)(u:V→V→V→ Deck.Part G 6): ∑ i∈w,∑ j∈w,∑ k∈w,u k i j=∑ i∈w,∑ j∈w,∑ k∈w,u i j k:= by
 conv_lhs=> arg 2; intro a; rw [Finset.sum_comm]
 rw [Finset.sum_comm]
lemma orb_one (a:Who G 6): D1 a (orbZ G)= ∑ x:Badge G,∑ y:Badge G,∑ z:Badge G, (3* tau x y z * ct x true a) • (Glyph y true*Glyph z true):= by
 let f(x y z:Badge G): Deck.Part G 6:=(tau x y z*ct x true a) • (Glyph y true*Glyph z true)
 have h(x y z:Badge G): D1 a (tau x y z • (Glyph x true*Glyph y true*Glyph z true))= f x y z+ f y z x+f z x y:= by
    unfold f; rw [tau_spin,tau_spin y, tau_spin x]; rw [show D1 a (tau x y z • _)= _ from (pderiv a).map_smul .., mul_assoc (Glyph ..)]; change tau x y z • D1 a (Glyph x true*(Glyph y true*Glyph z true))= _; rw [primg,primg,count_glyph]; simp only [smul_add,mul_add,ct,smul_eq_C_mul,map_mul]; ring
 have e(x y z:Badge G) : (3*tau x y z* ct x true a) • (Glyph y true*Glyph z true)=f x y z+ f x y z+ f x y z:= by unfold f; rw [show (3:ℂ)*tau x y z* _ = ((tau x y z*ct x true a)+(tau x y z*ct x true a)+(tau x y z*ct x true a)) from by ring, add_smul,add_smul]
 unfold orbZ D1; simp_rw [map_sum,show ∀ x y z:Badge G,_ = _ from h,e, Finset.sum_add_distrib]; rw [cyc _ _ f,← cyc _ _ (fun x y z=> f y z x)]
lemma orb_twice (a b:Who G 6): D1 a (D1 b (orbZ G))=∑ x:Badge G,∑ y:Badge G,∑ z:Badge G,(3 * tau x y z * ct x true b) • (ct y true a • Glyph z true+ ct z true a • Glyph y true):= by
 rw [orb_one]; unfold D1; simp only [map_sum,Derivation.map_smul];apply Finset.sum_congr rfl; intro _ _;apply Finset.sum_congr rfl; intro _ _;apply Finset.sum_congr rfl;intro j _; apply congrArg _; exact (primg ..).trans (by rw [count_glyph,mul_comm (Glyph _ _) (C _),C_mul'])
end YM.RG11.FirstW.Branch
