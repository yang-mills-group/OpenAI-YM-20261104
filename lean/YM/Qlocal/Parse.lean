import YM.Qlocal.Intro
/-!
Turn compressed coefficients into Leaf of appropriate kind, preserving *every*
mask and test. Real/imag pair on the **same** wing. Only one hull per mark
set, so avoid exponentiating the self of a log wing (`Menu.jets`); in
fact the missing term is always nilpotent-square. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Payload
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions MergeProof Menu Accent Lotus
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}
variable {dcl : Set (ℕ ×ℕ)} {Y:Taste Ω o P R} (hd : RetainsDeclared dcl Y s)
    (H:Peak P o Y c a A B) (ht:a=P.p.supportExponent)(hΩ:Ω)(hz:∀ i,0<c i) (Vw:Config G n)
local notation "TZ"=> Town R s
local notation "CZ"=> City R s
-- colors.S.F.Q temporary Radius.Intake. q tag charge. Post relative extraction receipts.T.
structure Fabric where
   light : Town R s→ℝ
   night : City R s→ℝ
   glows i : 0 ≤ light i
   shores i : 0 ≤ night i
   sees (i:Town R s) x V : ‖snow hd H hΩ x i V‖ ≤ light i
   casts (i:City R s) x V : ‖stars hd H hΩ x i V‖ ≤ night i
   photic : Ac.Hit (fun i:Town R s=> i.val.1.val) P.p.B (fun i=> c i.val.2.val * light i) a A
   eclipse : Ac.Hit (fun i:City R s=> i.val.1.support) P.p.B (fun i=> c i.val.2.val * night i) a B

include ht hz H
lemma existF : Nonempty (Fabric hd H hΩ):= by
 obtain ⟨l,hl,hL,hV⟩:= lights hd H ht hΩ hz; obtain ⟨v,hv,hT,hA⟩:= darks hd H ht hΩ hz; exact ⟨l,v,hl,hv,hV,hA,hL,hT⟩
omit ht hz H
noncomputable abbrev Light := (Fabric hd H hΩ)
set_option quotPrecheck false
local notation "A'"=> P.activities
local notation "P'"=> P.p

def paintSeat (x:TZ) : RegularAddress n:=⟨x.val.1.prop.choose,x.val.1.val,x.val.1.prop.choose_spec⟩
def lightKey (x:TZ):= blankRow n (paintSeat x,pin x)
def nightKey (G:Gauge)(x:CZ):= sleepK G n (x.val.1,pin x)
def side : Bool→ ℂ→L[ℝ] ℝ:=fun i=> if i then Complex.imCLM else Complex.reCLM
def colour (i:Bool):ℂ:=if i then Complex.I else 1
lemma side_le (i:Bool)(x:ℂ): ‖side i x‖ ≤ ‖x‖ := by
 cases i; exact Complex.abs_re_le_norm _; exact Complex.abs_im_le_norm _
lemma pairAm (x:ℂ) : ∑ i:Bool, (side i x:ℂ)*colour i=x:=by rw [Fintype.sum_bool]; simp only [colour,side,Complex.imCLM_apply,Complex.reCLM_apply,Bool.false_eq_true,if_true,if_false,mul_one]; rw [add_comm]; exact Complex.re_add_im _
lemma colour_norm (i:Bool): ‖colour i‖=1:=by cases i <;> simp [colour]
lemma light_inj : Function.Injective (lightKey (R:=R) (s:=s)):= fun _ _ he=>pin_injective (Prod.mk.inj ((blankRow n).injective he)).2
lemma night_inj : Function.Injective (nightKey G (R:=R) (s:=s)):= fun _ _ he=>pin_injective (Prod.mk.inj ((sleepK G n).injective he)).2
abbrev deck (R:Census V)(s:V→Support n) := (Town R s× Bool) ⊕ (City R s × Bool)
local notation "DK"=> deck R s
variable (hp: HasSlots P.p P.activities)
include hp
lemma lightSeat (i:TZ): P.activities.reg (lightKey i)=paintSeat i:= by rw [hp.reg]; exact congr_arg Prod.fst (recorded ..)
lemma nightSeat (i:CZ): barcode P.activities (nightKey G i)=citybox i:= by
 have h:readFoot (P.activities.forced (nightKey G i))=i.val.1:=by rw [hp.forced]; exact tile_exact ..
 exact Prod.ext (congr_arg Foot.support h) (congr_arg Foot.inventory h)
variable {hd H hΩ} (Yw: Fabric hd H hΩ)
local notation "L₀"=> snow hd H hΩ
local notation "L₁"=> stars hd H hΩ

def latte (x:Ω)(i:TZ×Bool): Hat R P where
  s := i.fst.val.2.val
  shiny := i.fst.val.2.prop
  M := { turn:= Wing.logKey (lightKey i.fst), ingredient:= side i.2 ∘ (snow hd H hΩ x i.1), weight:=Yw.light i.1
         borel := (side i.2).continuous.measurable.comp (snow_fit hd H hΩ x i.1|>.1.measurable)
         glows:= fun u V=> congr_arg (side i.2) (snow_fit hd H hΩ x i.1|>.1.invariant u V)
         earn:= fun V=> (side_le _ _).trans (Yw.sees _ _ _)
         blank:= hp.regular _
         scopedR:= by rw [Wing.support,lightSeat hp]; exact fun u v he hf=> congr_arg (side i.2) (snow_fit hd H hΩ x i.fst|>.1.reads _ _ he hf)
         grant:=fun X hx=> by rw [Wing.qualifies,lightSeat hp]; apply (snow_fit hd H hΩ x i.fst).2 _; intro ht; apply hx; dsimp only [Function.comp_apply]; rw [ht,map_zero] }
  charge:= colour i.2

def decaf (x:Ω)(i:CZ×Bool): Hat R P where
  s:= i.fst.val.2.val
  shiny:= i.fst.val.2.prop
  M:={ turn:= Wing.gasKey (nightKey G i.fst)
       ingredient:= side i.2 ∘ stars hd H hΩ x i.1
       weight:= Yw.night i.1
       earn:= fun V=> (side_le _ _).trans (Yw.casts _ _ _)
       glows:=fun u V=> congr_arg (side i.2) (stars_fit hd H hΩ x i.1|>.1.invariant u V)
       borel:= (side i.2).continuous.measurable.comp (stars_fit hd H hΩ x i.1|>.1.measurable)
       blank:= trivial
       scopedR:= by rw [Wing.support,show (P.activities.forced _).support= _ from (?_: (P.activities.forced (nightKey G i.fst)).support=i.fst.val.1.support)]; swap; · exact congr_arg Prod.fst (nightSeat hp _)
                    exact fun u v he hf=> congr_arg (side i.2) (stars_fit hd H hΩ x i.1|>.1.reads _ _ he hf)
       grant:= fun X hx => by
           have he : i.1.val.1.support ∩ flags P.p.threshold X=i.1.val.1.inventory:= (stars_fit hd H hΩ x i.1).2 _ (fun h=>hx (by dsimp only [comp_apply]; rw [h,map_zero])); refine ⟨?_,?_⟩
           · rw [show (P.activities.forced _).support=i.1.val.1.support from congr_arg Prod.fst (nightSeat hp i.1), show (P.activities.forced _).inventory=i.1.val.1.inventory from congr_arg Prod.snd (nightSeat hp i.1)]; exact he
           rw [hp.forced]; exact (tile_test ..).2 he }
  charge:= colour i.2

def profileH (x:Ω): deck R s→ Hat R P:= Sum.elim (latte hp Yw x) (decaf hp Yw x)
local notation "G!"=> profileH hp Yw
omit hp
abbrev kind (i:DK): R.Mode:= Sum.elim (fun j : TZ×Bool=> (j.1.val.2.val)) (fun j:CZ×Bool=> j.1.val.2.val) i
abbrev valueH (i:DK):ℂ:= Sum.elim ((fun i=> colour i.2):TZ×Bool→ ℂ) ((fun i=>colour i.2):CZ×Bool→ℂ) i
include hp
include H hd
lemma signs : Sign (kind (R:=R) (s:=s)) s (fun i:DK=> (G! hΩ i).M.crest) := by
 constructor; · rintro (⟨ ⟨⟨b,⟨x,hv⟩⟩,p⟩,i ⟩|⟨⟨⟨z,⟨u,hk⟩⟩,p⟩,i⟩); exact hv; exact hk
 rintro (⟨z,x⟩|⟨z,x⟩)
 · have hx := lightSeat hp z; change speech z.val.2.val (P.activities.reg (lightKey z)).support s; rw [hx]; exact z.prop
 change speech z.val.2.val (P.activities.forced (nightKey G z)).support s; rw [show (P.activities.forced _).support=z.val.1.support from congr_arg Prod.fst (nightSeat hp z)]; exact z.prop

lemma roster : Roster (fun i=>(G! hΩ i).M) (fun x i=>(G! x i).M):= by constructor; all_goals rintro x (i|i) <;> rfl
lemma modesH x (i:deck R s): (profileH hp Yw x i).s=kind i:= by cases i<;> rfl
lemma chargesH x (i:deck R s):(profileH hp Yw x i).charge=valueH i:= by cases i<;>rfl
lemma worthH x (i:deck R s): ‖(profileH hp Yw x i).charge‖=1:= by rw [chargesH]; cases i <;> exact colour_norm _
lemma income (x:Ω): Ac.Hit (fun i: deck R s=>(G! x i).M.crest) P.p.B (fun i=> c (G! x i|>.s)*(G! x i).M.weight) a (2*(A+B)):= by
 intro i; let Y(i:DK):= G! x i; let f j:= if i∈ (Y j).M.crest then c (Y j).s * (Y j).M.weight * Real.exp (a * coverNumber P.p.B (Y j).M.crest) else 0
 have hv (j:TZ)(b:Bool):(Y (.inl (j,b))).M.crest=j.val.1.val:= congr_arg RegularAddress.support (lightSeat hp _)
 have he (j:CZ)(b:Bool):(Y (.inr (j,b))).M.crest=j.val.1.support:= congr_arg Prod.fst (nightSeat hp _)
 let p(i:TZ):= i.val.1.val; let g(j:TZ):= if i∈p j then c j.val.2.val*Yw.light j*Real.exp (a * coverNumber P.p.B (p j)) else 0; have ht : SumBudget g A:= Yw.photic i
 let q j:= (j:CZ).val.1.support; let h(j:CZ):= if i∈q j then c j.val.2.val*Yw.night j*Real.exp (a*coverNumber P.p.B (q j)) else 0; have hy: SumBudget h B:= Yw.eclipse i
 have hL(j:TZ×Bool): f (.inl j)=g j.1:= by unfold f; simp only [hv]; rfl -- pattern match j
 have hK(j:CZ×Bool): f (.inr j)= h j.1:= by unfold f; simp only [he]; rfl
 change SumBudget f _; refine budget_finite ?_ ?_; rotate_left
 · change ∑ i: (TZ×Bool) ⊕ (CZ×Bool), f i ≤ _; rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]; simp_rw [hL, hK,Fintype.sum_bool,Finset.sum_add_distrib]; linarith only [budget_sum ht univ,budget_sum hy univ]
 rintro (j|j); rw [hL]; exact ht.1 _; rw [hK]; exact hy.1 _

end YM.Qlocal.Payload

namespace YM.Qlocal.Payload
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions MergeProof Menu Accent Lotus
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ Λ φ:ℝ}
    {dcl : Set (ℕ ×ℕ)} {Y:Taste Ω o P R} {hd : RetainsDeclared dcl Y s}
    {H:Peak P o Y c a A B} (ht:a=P.p.supportExponent){hΩ:Ω}(hz:∀ i,0<c i)
local notation "TZ"=> Town R s
local notation "CZ"=> City R s
local notation "DK"=> deck R s
variable (hp: HasSlots P.p P.activities)(Yw: Fabric hd H hΩ) (x:Ω)(Vw:Config G n)
set_option quotPrecheck false
local notation "H0"=>profileH hp Yw x
local notation "TA"=> Y.menu.terms x
local notation "B0"=>Real.exp (P.exponent Vw)

include hp
lemma cameras : ∑ i:Town R s,Poly.send i.val.2.val (snow hd H hΩ x i Vw)= roll H0 Vw :=by
 rw [perfumes]; unfold deck; rw [Fintype.sum_sum_type]; have hh(x':CZ×Bool): odour (H0 (.inr x')) Vw=0:= by unfold odour prose; rw [show (H0 (.inr x')).M.turn= .gasKey _ from rfl]; rw [zero_mul,Poly.send_zero]
 simp_rw [hh]; rw [Finset.sum_const_zero,add_zero,Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _=> ?_
 let a:= snow hd H hΩ x i Vw
 rw [Fintype.sum_bool]; change Poly.send _ a=Poly.send i.val.2.val ((side true a:ℂ)*colour true)+ Poly.send i.val.2.val (((side false a):ℂ)*colour false); rw [← send_add, ← Fintype.sum_bool (fun i=> (side i a:ℂ)*colour i), pairAm] -- check orientation.
lemma lighters_eq {j:ℕ} (b:DK) : WKey (H0 b)=.logKey j → ∃ i : Town R s,i.val.2.val=(H0 b).s ∧ j=lightKey i:= by
 rintro hh; rcases b with i|i; exact ⟨i.1,rfl,(Wing.logKey.inj hh).symm⟩; exact False.elim ((show ¬ Wing.gasKey _ = Wing.logKey j from fun h=>Wing.noConfusion h) hh)
variable [Fintype V]
include ht hz
set_option maxHeartbeats 700000 in
lemma deck_reads : jets (H0) Vw=Poly.pass ((Y.menu.terms x).extra Vw):=by
 have hr:= log_measured hd H ht hΩ hz Vw x; rw [show (Y.menu.terms x).extra Vw= roll H0 Vw from hr.trans (by convert! cameras hp Yw x Vw)]
 let p:= H0; let f(i:ℕ):= rush p (.logKey i) Vw; let S : Finset ℕ:= logDeck (H0)
 have h: ∀ i:S, ∃ θ:R.Mode, θ.val.Nonempty ∧ ∀ j:DK,WKey (H0 j)=.logKey i.val→ (H0 j).s=θ:= by
   intro i; obtain ⟨b,hb⟩:= (cams p i.val).1 i.prop; obtain ⟨a,ha,hV⟩:=lighters_eq hp Yw x b hb
   refine ⟨(H0 b).s,(H0 b).shiny,fun j hj=> ?_⟩; obtain ⟨z,hz',hZ⟩:= lighters_eq hp Yw x j hj; exact hz'.symm.trans ((light_inj (hZ.symm.trans hV)) ▸ ha)
 choose q hq hg using h
 let g(i:S):=(f i.val).part (q i); have he (i:S): Poly.send (q i) (g i)= f i.val:= by
    ext a; rw [Poly.part_send]; by_cases ht:a=q i; · rw [ht,if_pos rfl]
    rw [if_neg ht]; unfold f rush; rw [Poly.part_sum]; symm; apply sum_eq_zero; intro j _; split; next hh=> rw [varnish,Poly.part_send, if_neg (mt (fun he=> he.trans (hg i j hh)) ht)]
    next=>rfl
 unfold jets roll; rw [← prod_coe_sort S,← sum_coe_sort S]; change (∏ i:S, (1+f i.val))=Poly.pass (∑ i:S,f i.val); simp_rw [← he, Extra.Trajectories.pass_sum univ q (fun i _=>hq i) g]

omit hz ht in
lemma patio (i : Box n): board H0 i Vw=
    ∑ j: CZ, if citybox j=i then Poly.send j.val.2.val (stars hd H hΩ x j Vw) else 0:=by
 rw [patron]; unfold deck; rw [Fintype.sum_sum_type]; have hε(b:TZ×Bool): fragrance (H0 (.inl b)) Vw i=0:= by unfold fragrance MergeProof.entry; rw [show (H0 (.inl b)).M.turn= .logKey _ from rfl,zero_mul,Poly.send_zero] -- match
 simp_rw [hε]; rw [sum_const_zero,zero_add, Fintype.sum_prod_type]; refine sum_congr rfl (fun j _=>?_); let a:= stars hd H hΩ x j Vw; unfold fragrance MergeProof.entry; simp_rw [show ∀ b:Bool, (H0 (.inr (j,b))).M.turn= .gasKey (nightKey G j) from fun _=> rfl, nightSeat hp]
 split
 next h=> change (∑ b:Bool,Poly.send j.val.2.val ((side b a:ℂ)* colour b)) = Poly.send j.val.2.val a; rw [Fintype.sum_bool,← send_add,← Fintype.sum_bool (fun i=>(side i a:ℂ)*colour i),pairAm]
 next h=> simp

variable (hP:P.Lawful φ Λ d b δ) {c₀:Side} (S:StepData c₀ n)
include hP

lemma borrows (r:V→ℝ)(hw:∀ i,0<r i) : MergeProof.Menu.Expense H0 r S Vw=(Y.leaf x).contents.density Vw :=by
 unfold Expense; rw [passIn H0 S hP hw,deck_reads ht hz hp Yw]; unfold Overlay.Bands.density; congr 2
 rw [show ((Y.leaf x).contents).cluster Vw=field (cram (barcode P.activities) (fun i=>(TA).each i Vw)) (flags P.p.threshold Vw) from (_ : _), show (fun i=> bar P.activities R Vw i+_)=_ from (?_: (fun i=>bar P.activities R Vw i+ board H0 i Vw)=cram (barcode P.activities) (fun i=>(TA).each i Vw))] -- syntax
 · apply funext; intro j; rw [(pocket H ht hz Vw x hP.labels r hw|>.2), flag_measured hd H ht hΩ hz Vw x, patio hp Yw]; congr!
 exact (Accent.rock_out P.activities P.p Vw (fun i=>(TA).each i Vw) hw (pocket H ht hz Vw x hP.labels r hw|>.1)).symm
end YM.Qlocal.Payload
