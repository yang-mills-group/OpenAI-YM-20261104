import YM.RegulatorIR.Profiles.Trek
import YM.PertExtension.BareSlot

/-!
# Turn genuine native cylinder stencils into finite regulator germ symbols

Do NOT use `sameColumns` repricing $N,p$ (would feed a physical rather
than formal coupling). Real fields with genuine gauge. Uses accepted common
frame/sections/Bid pop (construction of required section slots elsewhere).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Halo
open Labels Source Drops Bid
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I J X:Type}{r n m p q a b e d:ℕ}
attribute [local instance] Gauge.frobInner
section Genera
-- en route gauge invariance for Planet. Allow derivatives and path fields
structure LocalStamp (B: Portrait G) (m:ℕ): Prop where
 people : Person B
 crown : ∃ S: Finset Cover,∀ t, LocalOn S (B t)
 order : ∀ v, Tested.Bill m (outing G B v)
variable {B:Portrait G}(C:LocalStamp B m)
include C
lemma stamp_symbol : ∃ T: Orders (Foot G), Halo.BasisT m m B T ∧ Ranks m T:=by
 let F:Micro (Foot G):= fun z v=> B z (win G v); let x(v):= outing G B v
 have hp(v): flank F v=x v:= rfl
 have hc : Nonempty (Run F):=by
    obtain ⟨p,h⟩:= C.crown
    let S:Finset (Foot G):= (p×ˢ Finset.univ) ×ˢ Finset.univ
    let L(w: ℝ× (↥S→ℝ)):=F w.1 (fill (placeFin S) w.2)
    refine ⟨{ J:=↥S,fin:=inferInstance,inc:=placeFin S, script:=L,smooth:=?_,reaches:=?_}⟩
    · apply C.people.neat; intro i; unfold win; exact (G.exp_jet.contDiffAt.comp _ (((tall S i).contDiffAt).comp (f:=Prod.snd) (0:ℝ×(↥S→ℝ)) contDiffAt_snd)).of_le le_top
      exact contDiffAt_fst; rfl
      have hh: fill (placeFin S) 0=0:= (liftFill (placeFin S)).map_zero;change win G (fill _ 0)=1; rw [hh]; ext1 i; change G.lieExp (0:G.Color)= _;simp
    intro t v; unfold L F; dsimp only; apply h; intro i hi _; apply congr_arg G.lieExp; ext1 j; exact (fill_eq S (i,j) (Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,Finset.mem_univ _⟩) v).symm
 obtain ⟨w⟩:=hc
 choose Q hs hv hh using fun j:ℕ=>mold_jet w.script (j+m)
 let T(j:ℕ):Ranked (Foot G):=fun r=>offer w.inc (Q j r)
 refine ⟨T,⟨C.people,fun _ _=>bound_offer .., fun i j=>offer_symm w.inc _ (hs i j),?_⟩, fun i j hi=> hv i j (fun h'=> hi (by unfold T;rw [h']; ext x;simp [offer,Stalk.collect]))⟩
 intro v; change tale (flank F v)= _; ext i; rw [coeff_X_pow_mul']
 split_ifs with hg
 · rw [shelter,coeff_mk,w.flank_v, inscription,coeff_mk,← Nat.sub_add_cancel hg]
   -- proof simp subtraction nested
   simp only [add_tsub_cancel_right]; unfold T; rw [flute]
   exact hh (i-m) _
 exact (Script.actual (w.smooth_v v)).vanish (C.order v) (by omega)

omit C
lemma LocalStamp.moves {t : Cover}(C:LocalStamp B m) : LocalStamp (convey t B) m:=by
 obtain ⟨z,H⟩:= C.crown
 refine ⟨C.people.vayne t,⟨z.image (fun x=>x+t),?_⟩,fun v=> ?_⟩
 · intro _ i j h; apply H; intro u hz ha; apply h
   · exact Finset.mem_image.mpr ⟨_,hz,rfl⟩
   apply Finset.mem_image.mpr ⟨_,ha,?_⟩; change u.1+Lattice.step _+t=u.1+t+_;abel
 rw [show outing G (convey t B) v= outing G B (v ∘ carryX t) from funext fun i=>congr_arg (B i) (carrier ..)]; exact C.order _

def guardP (B:Portrait G)(f:ℝ→ℝ): Portrait G:= fun t u=> f t * B t u
lemma LocalStamp.dresses {f:ℝ→ℝ}(C:LocalStamp B m)(h:Continuous f)(H:ContDiffAt ℝ ∞ f 0)(hf: Tested.Bill a f) : LocalStamp (guardP B f) (a+m):=by
 obtain ⟨p,hp⟩:= C.crown
 refine { people:= ⟨(h.comp continuous_fst).mul C.people.cap, fun t g u=>congr_arg (fun v=> f t*v) (C.people.guise t g u), ?_⟩, crown:=⟨p,fun t U V h=> congr_arg (fun v=>f t*v) (hp t U V h)⟩, order:=fun v=> Tested.bill_mul hf (C.order v) }
 intro E _ _ b U ho hb hn hv
 apply ContDiffAt.mul (g:= fun i:E=>B (b i) (U i)) _ (C.people.neat b U ho hb hn hv)
 exact (show ContDiffAt ℝ ∞ f (b 0) from hn.symm ▸ H).comp 0 hb
end Genera

section Field
variable {F: Labels.Frame G d}(T:SectionData F){H: Hol G}
-- Analytic projection and Laurent order
lemma walk_sense {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→CoverConfig G)(h:∀ i:Edge Cover,ContDiffAt ℝ ∞ (fun x:E=>G.mat (U x i)) 0)(p:Cover)(w:Walk):ContDiffAt ℝ ∞ (fun x:E=> G.mat (travel (U x) p w)) 0:=by
 induction w generalizing p with
 | nil=>exact contDiffAt_const
 | cons a w ih=>
    simp only [travel, G.mat_mul]; apply ContDiffAt.mul _ (ih _); unfold Lattice.Step.read;split <;> first|exact h _| (simp_rw [G.mat_inv];exact (starL' ℝ).contDiff.contDiffAt.comp _ (h _))
lemma sensor {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→CoverConfig G)(h:∀ i,ContDiffAt ℝ ∞ (fun x:E=>G.mat (U x i)) 0)(b:RG.Slot): ContDiffAt ℝ ∞ (b.eval ∘ U) 0:=by
 let V(x):=faceValue (U x) (b.offset,b.plaq);let K:= LinearMap.toContinuousLinearMap G.projectColor;let Q:= LinearMap.toContinuousLinearMap G.colorMat
 have he: ContDiffAt ℝ ∞ (fun x:E=> G.mat (V x)) 0:=walk_sense U h b.offset (square b.plaq.val.1 b.plaq.val.2)
 have ht: ContDiffAt ℝ ∞ (fun x:E=> G.curvature (V x)) 0:=by
    unfold curvature; simp_rw [G.mat_inv]; exact K.contDiff.contDiffAt.comp _ ((he.sub ((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff.contDiffAt.comp _ he)).const_smul (1/2:ℝ))
 let B(x):=G.mat (travel (U x) 0 b.walk);have hp: ContDiffAt ℝ ∞ B 0:=walk_sense U h 0 b.walk
 exact K.contDiff.contDiffAt.comp _ ((hp.mul (Q.contDiff.contDiffAt.comp _ ht)).mul ((starL' ℝ:G.Mat≃L[ℝ]G.Mat).contDiff.contDiffAt.comp _ hp))

private def prePose (V:Pose G m)(L: Fin m→RG.Slot)(U:CoverConfig G):= lumin V (mapped L U)
private lemma leftWing (V:Pose G m)(L:Fin m→RG.Slot)(U:CoverConfig G): prePose V L U= ∑ d∈V.support,(MvPolynomial.coeff d V) * ∏ r∈d.support, (Complex.ofReal ((mapped L U) r.1 r.2))^(d r):=by rw [prePose,lumin,MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]; rfl
lemma slotPlane (i: G.ColorIndex) : ContDiff ℝ ∞ (fun x:G.Color=> x i):=by
 convert! (contDiff_const (c:=EuclideanSpace.basisFun G.ColorIndex ℝ i)).inner ℝ (contDiff_id (E:=G.Color)) using 1
 ext1 x;exact (EuclideanSpace.basisFun_inner ..).symm
lemma drumSense {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→CoverConfig G)(h:∀ i,ContDiffAt ℝ ∞ (fun x:E=>G.mat (U x i)) 0)(V:Pose G m)(L:Fin m→RG.Slot): ContDiffAt ℝ ∞ (fun x=>prePose V L (U x)) 0:=by
 simp_rw [leftWing]; apply ContDiffAt.sum; intro i _; apply ContDiffAt.mul contDiffAt_const; apply contDiffAt_prod;intro j _; apply ContDiffAt.pow
 exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((slotPlane _).contDiffAt.comp _ (sensor U h (L j.1)))
lemma slotCash (v:Foot G→ℝ)(b:RG.Slot)(i:G.ColorIndex):Tested.Bill 1 (fun t:ℝ=>b.eval (win G (t • v)) i):=by
 let F(t:ℝ):=win G (t • v); let g(t):= b.eval (F t) i; have h:ContDiffAt ℝ ∞ g 0:=by
    refine (slotPlane i).contDiffAt.comp _ (sensor F ?_ b); intro j; unfold F win; simp_rw [timbers, Pi.smul_apply]; exact (G.exp_jet.contDiffAt.of_le le_top).comp _ (contDiffAt_id.smul contDiffAt_const)
 have hx:F 0=1:=by unfold F;rw [zero_smul];ext1 i;change G.lieExp (0:G.Color)=1;simp
 have hs : g 0=0:=by
    unfold g; rw [hx]
    have he:= SlotEvaluation.slot_zero (G:=G) (n:=8) (o:=0) b; rw [SlotEvaluation.zero_links] at he; exact congr_fun (congr_arg (fun x:G.Color=>(x: G.ColorIndex→ℝ)) he) i
 change Tested.Bill 1 g
 convert zero_first h hs (1:ℝ) using 1;ext;simp
lemma stencil_price (v:Foot G→ℝ)(V:Pose G m)(L:Fin m→RG.Slot)(h:lows V a): Tested.Bill a (fun t=> prePose V L (win G (t • v))):=by
 let f (i:Fin m × G.ColorIndex)(t:ℝ):=Complex.ofReal ((mapped L (win G (t • v))) i.1 i.2); let s:=V.support; let p(z:Fin m × G.ColorIndex→₀ℕ):= (fun _=>MvPolynomial.coeff z V)* (∏ i∈z.support, f i ^ z i)
 have hp i: Tested.Bill 1 (f i):=by
    obtain ⟨r,hr,he⟩:=slotCash v (L i.1) i.2; exact ⟨r,hr,he.mono fun x hx=> by simpa only [f,mapped, Complex.norm_real] using hx⟩
 simp_rw [leftWing]
 have hq: Tested.Bill a (∑ i∈s,p i):=by
    apply bill_sum; intro i hi; have hc:= h i hi; unfold p; apply bill_ge (bill_mul (bill_const _) (bill_product i.support (fun z=>i z*1) _ (fun _ _=> bill_pow (hp _) _))); simpa only [Nat.mul_one,Nat.zero_add,Finsupp.sum] using hc
 convert hq using 1; ext1 t; simp [s,f,p,Finset.sum_apply, Finset.prod_apply]

def bare (i:F.Index): Portrait G:= fun _ U=> (T.evaluate (Pi.single i 1) U).re
variable (A:T.Sound H)(B:Bid.pop T)
include A B
lemma authentically (i:F.Index): LocalStamp (bare T i) (F.grades i).2 :=by
 obtain ⟨a,p,_,v,h,hv⟩:= B i
 refine { people:= ⟨Complex.continuous_re.comp ((T.continuous_evaluate _).comp continuous_snd),fun t g u=>congr_arg Complex.re (A.gaugeInvariant _ g u),?_⟩, crown:=⟨T.stencil,fun _ U V h=> congr_arg Complex.re (T.cylinder_local _ U V h)⟩, order:=?_ }
 · intro E _ _ b U hp hb hh hc; unfold bare; rw [h]; exact Complex.reCLM.contDiff.contDiffAt.comp _ (drumSense U hp v p)
 intro x; unfold outing bare; rw [h]; obtain ⟨c,hc,Hc⟩:= stencil_price x v p hv; refine ⟨c,hc, Hc.mono (fun y hy=> ?_)⟩; exact le_trans (b:=‖prePose v p (win G (y • x))‖) ((Real.norm_eq_abs _).le.trans (Complex.abs_re_le_norm _)) hy

omit A B in
lemma genuinely_real (A:T.Sound H)(i:F.Index)(x:CoverConfig G)(t:ℝ):T.evaluate (Pi.single i 1) x= (bare T i t x:ℂ):=by
 apply Complex.ext; rfl
 have hp:=A.ordinary_real (Pi.single i 1) x; have ht:star (Pi.single i 1 : F.Coeff)=Pi.single i 1:=by ext1 a;simp [Pi.single_apply]
 rw [ht] at hp; exact Complex.conj_eq_iff_im.mp hp.symm
end Field
end YM.RegulatorIR.Profiles
