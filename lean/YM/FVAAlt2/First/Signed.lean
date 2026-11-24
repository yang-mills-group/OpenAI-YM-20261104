import YM.FVAAlt2.First.Market
import YM.FVAAlt2.Convert.Agree
/-! Signed-index budget for high Taylor fees together with Genome/unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Draft MS.Native.Orient MS.Menus MS.Local.Physical MS.Land MS.FVA MS.FVA.Town MS.FVA.Motions
open MS.Book MS.Book.Convolve MS.Native.Paint MS.Native.Wilsonian MS.Plane MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open MS.Logarithm MS.Book.Program
open Pert Pert.Orb SchemeRG11 SchemeRG11.Atoll SchemeRG11.Haze SchemeRG11.Pile SchemeRG11.Sway
open MvPolynomial
open FormalOPE.RG10 Maxwell Convert Home Patho
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius PowerSeries Classical Matrix
variable {G: Gauge}{d k:ℕ}{F: Frames G}{n:Side}{p q:pLabel G}{B: Deck G} {i:Glyph B d}
local notation "Φ"=> Dot G Cover
-- transform in all horizontal rows. off-shell physically-rebased stencils
variable (s:Signed)
lemma homogeneous_move (j:ℕ)(p:pLabel G): title s (homogeneousComponent j p)= homogeneousComponent j (title s p) := by
 apply Outlook.solder; rw [Patho.enrole, ← harness, ← harness, Patho.enrole ]; unfold Labels.rotated; let P (k:ℕ):= (Labels.Taylor.turn (G:=G) (j:=k) s.ortho⁻¹)
 let L:= realCast p
 have hm(q: Pol G): Labels.changed P (homogeneousComponent j q)= homogeneousComponent j (Labels.changed P q):= by
   -- same as color stencil proof; commutes hom at same generation
   conv_lhs=> rw [ ← q.support_sum_monomial_coeff ]
   conv_rhs=> rw [ ← q.support_sum_monomial_coeff ] -- semicolon eats rhs?
   simp_rw [ _root_.map_sum ]; apply Finset.sum_congr rfl; intro u hu; let Q:= monomial u (q.coeff u); have hv:Q.IsHomogeneous u.degree:=isHomogeneous_monomial _ rfl
   have he: (Labels.changed P Q).IsHomogeneous u.degree:=by rw [Finsupp.degree_eq_weight_one]; exact Labels.pure_moved (fun _=>1) P u (q.coeff u)
   change Labels.changed P (homogeneousComponent j Q)=homogeneousComponent j (Labels.changed P Q); rw [homogeneousComponent_of_mem hv,homogeneousComponent_of_mem he]; split <;> simp
 apply hm
lemma clip_move (p:pLabel G)(j:ℕ): title s (clip j p)=clip j (title s p):= by simp_rw [ clip,LinearMap.comp_apply, homogeneous_move ]; unfold title winds; rw [ Dose.night,Patho.talem ]
lemma in_port (p:pLabel G)(U:Config G n): sensorMap (0:Site n) p (Lattice.pull s 0 U)=sensorMap 0 (title s p) U:= by apply Complex.ofReal_injective; rw [saw_real,saw_real,terrain,Bare.exact_tensor,Lattice.affine,Signed.act_zero,zero_add,terrain,Patho.enrole] -- order
lemma resident_m (p:pLabel G): Orient.pose s (resident p)=resident (title s p):= by
 have hh(p:pLabel G)(n:Side): shown n (resident p) = MS.Cylinder.region.symm (reads (sensorMap 0 p ∘ nation)):= Subtype.ext ((parallels p).born n).home
 apply (markEq ..).mp; apply Eventually.of_forall; intro n; rw [travel_t,hh,hh]; apply Subtype.ext; rw [pose_rule s ( (parallels p).born n|>.born ) ]; apply congr_arg (_root_.YM.MS.Native.reads) -- suspect Namespace
 funext i; simp_rw [Function.comp_apply,at_nation,in_port]
lemma total_act (p:pLabel G): Orient.pose s ∘ (total k p)= total k (title s p):=by
 funext i; simp only [Function.comp_apply,total,cereal,levels, Finset.sum_apply, _root_.map_sum ]; simp only [poseModel,resident_m,clip_move]
-- HEIGHT-only signed ribbon. appointment.B.Present.Intentional
section funds
variable {J:Type}[Fintype J]
lemma total_plus (f g:pLabel G):total d (f+g)=total d f+total d g:=by unfold total; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; funext n; simp [cereal,levels,formed_add]
lemma total_smu (c:ℝ)(p:pLabel G): total d (c • p)=(c:ℂ) • total d p:=by unfold total; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; funext n; simp only [cereal, levels, _root_.map_smul, formed_smul,Pi.smul_apply]
lemma total_z : total d (0:pLabel G)=0:= (_root_.add_eq_left.mp (Eq.symm (show total d (0:pLabel G)=total d 0+total d 0 from by nth_rw 1 [← zero_add (0:pLabel G), total_plus]))) -- orientation
set_option linter.unusedSectionVars false
lemma total_sum (I:Finset J)(f:J→pLabel G): total d (∑ i∈I,f i)=∑ i∈I,total d (f i):=by
 induction I using Finset.induction_on with| empty => simp only [Finset.sum_empty,total_z]| insert i j he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,total_plus,ih]
lemma realCast_sum (I:Finset J)(f:J→pLabel G): realCast (∑ i∈I,f i)=∑ i∈I,realCast (f i):= map_sum _ f I
lemma realCast_scalar (p:pLabel G)(c:ℝ): realCast (c • p)= (c:ℂ) • realCast p:= by rw [MvPolynomial.smul_eq_C_mul, realCast,_root_.map_mul,map_C, MvPolynomial.smul_eq_C_mul];rfl
end funds
variable (P:FormalOPE.RG10.Position.Plan F)
local notation "Y"=> Home.seats P.liftOff P.certified
local notation "R"=> ExtraBook Y
local notation "V"=> Plaid Y
local notation "C"=> Home.stepR F Y
local notation "K"=> Home.localStep F Y
lemma title_act(i:V d): title s (price i.2)=∑ j:V d, Convert.roster F Y d s i j • price j.2 := by
 apply Outlook.solder; rw [Patho.enrole,realCast_sum]; simp_rw [ price_is, realCast_scalar, price_is, Convert.real_price ] -- twice maybe simp_rw stuck
 rw [show (Shop.seat Y i.snd).val=(P.liftOff.lift d (Home.mast Y d F (Land.read i))).val from by rw [  show mast Y d F (Land.read i)=_ from Home.pegl i,Home.mast_lifts ];rfl]
 change (Labels.tensor s.ortho ( P.liftOff.lift d _ )).val=_; rw [P.certified.oriented,show s.ortho=Signed.inclusionO s from rfl,← Home.toll F s i,map_sum, Submodule.coe_sum ]; refine Finset.sum_congr rfl fun j _=>?_; rw [map_smul]; change (K d s i j) • ( P.liftOff.lift d (Home.mast Y d F ( Land.read j )) ).val=_; rw [ show mast Y d F (Land.read j)=_ from Home.pegl j,Home.mast_lifts ];rfl
lemma forms_head (i:V d): Orient.pose s ∘ ((R).menu _ _ i.2)=∑ j:V d, K d s i j • ((R).menu _ _ j.2):= by
 unfold ExtraBook; dsimp only; rw [total_act, title_act s P i,total_sum]; apply Finset.sum_congr rfl; intro j hj; rw [ total_smu,Convert.real_price ]; by_cases he:i.1=j.1; · rw [he]
 rw [show K d s i j=0 from Convert.ele_zero (F:=F) s i j ?_,zero_smul,zero_smul]; exact fun h=> he (Fin.ext h) -- type!

lemma whole_bill (i: Glyph Y d) : Orient.pose s ∘ (R).menu _ _ i.2.2=∑ j:Glyph Y d, ((C d s) i j:ℂ) • (R).menu _ _ j.2.2:= by
 have hn:= high i; let E:= i.size; have he : Orient.pose s ∘ _= _:= forms_head s P (d:=E) i.2; apply he.trans; let f:=fun j:Glyph Y d=> ((C d s) i j:ℂ) • (R).menu _ _ j.2.2; let v(j:V E):= up (B:=Y) hn (Land.read j); have hu : Injective v:= fun _ _ ht=> eq_of_heq (Sigma.mk.inj (up_inj _ ht)).2; refine Eq.trans (b:= ∑ j:V E, f (v j) ) ?_ ?_
 · refine Finset.sum_congr rfl fun j _=>?_ ; unfold f; refine congr_arg₂ (· • ·) ?_ rfl
   unfold v; rw [movesOn]; have H:= climb_eq F s hn ( Land.read (B:=Y) i.2 ) ( Land.read j ); rw [show up hn (Land.read i.2)=i from Eq.symm (lampu i hn)] at H; exact H.symm -- wrong occurrence
 rw [← Finset.sum_image (f:=f) hu.injOn]; apply Finset.sum_subset (Finset.subset_univ _); intro j _ hj; unfold f; rw [ only_r F s _ _ (fun H=>?_) , Complex.ofReal_zero, zero_smul ]; obtain ⟨⟨j,h⟩,u⟩:=j; have he:j=E:= congr_arg Prod.fst H.symm; subst j; exact hj (mem_image.mpr ⟨ u,mem_univ _,rfl⟩)
lemma preamble_H (T:Team): formsH R T s (C d s):= by
 intro i x k; unfold Glyph.preamblePl; rw [ show Orient.pose _ _= Native.Wilsonian.wobble G T x (Orient.pose s ∘ (R).menu _ _ i.2.2) k from congr_fun (FVA.City.wob_train (s:=s) T x _) k ,whole_bill]; simp [map_sum,map_smul] -- watch parser & argument

-- rank-zero unit guaranteed. No fee hypothesis.
lemma gold_first (b:ℝ): total 0 ( MvPolynomial.C b:pLabel G )= (b:ℂ) • gold G:= by
 unfold total; simp_rw [zero_add,Finset.sum_range_one,cereal]; rw [ show clip 0 (MvPolynomial.C b:pLabel G)=MvPolynomial.C b from high_component _ (isHomogeneous_C (σ:=Key G) b),formed_C ]; funext n; have he:= gold_l (G:=G) n; unfold levels; rw [map_smul]; exact congr_arg ((b:ℂ) • ·) he
lemma humble : Genesis (ExtraBook B):= by
 intro i c h; have hh:i.1.val=0:= le_antisymm (Glyph.memory (Land.read i)) (Nat.zero_le _)
 let p:= price i.2; have hp:p.IsHomogeneous 0:=by rw [ ← hh ]; exact weightR ( price_grade i.2 ) -- dependent `rw`?
 let b:ℝ:= p.coeff 0; have he:(ExtraBook B).menu _ _ i.2= ( b:ℂ ) • gold G:=by change total i.1.val p = _; rw [ hh, show total 0 p=total 0 (MvPolynomial.C b) from congr_arg (total 0) (totalDegree_eq_zero_iff_eq_C.mp ((Nat.eq_zero_of_le_zero hp.totalDegree_le))), gold_first ];
 have ht:=(ExtraBook B).rich 0 _ i.2|>.ono; have hx:= Fits.smul (b:ℂ) (Fits.unit (G:=G) (b:=false)); rw [ he, show B.raw ((0:ℕ):ℤ) i.1.val i.2= _ from h, Pi.smul_apply,gold,if_pos rfl,hh ] at ht
 have hv:= fit_determines hx ht; have hZ:(b:ℂ)=(c:ℂ):= by simpa [coin] using congrFun hv []
 rw [he,hZ]
variable {U:Booked (seats P.liftOff P.certified)}
theorem lpt_launch (X: MS_Data G U) (he:Spect F U)(g:G.Simple) : ∃ Ξ:Prescription Y, Launch R X (F:=F) Ξ:= build_L (ExtraBook Y) X g humble he fun s t _=> preamble_H s P t
end YM.FVAAlt2.Pairing
