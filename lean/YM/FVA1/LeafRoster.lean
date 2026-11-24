import YM.FVA1.Reprice

/-! Supply the input menu without any leaf/blank-key assumptions on the input kernels.
This version is for FINITELY many rendered entries at a given n (uniform in their
number under the hit price). Origins/stubs can wrap, supports are periodic, old
forcing at each entry can be on a nonzero vacuum label and pays on it even though
we compact it by barcode during loan.
-/

noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent Menu Merge Merge.Palette
open Push Push.AbsoluteSums PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V T I:Type}[DecidableEq V]{Γ:Census V}
variable {G:Gauge}{n:Side}{P:RG.Rep G n}

/-- Each entry chooses a new fenced stencil for a regular source kernel (left),
or an actual old forced label (right). -/
abbrev Seal (n:Side):= Support n ⊕ ℕ

def Seal.scope (P:RG.Rep G n)(s:Seal n):Support n:= s.elim id fun i=>(P.activities.forced i).support

def modeOf (s:Seal n) : Bool:= s.elim (fun _=>false) (fun _=>true)

structure Page {V:Type} [DecidableEq V] (Γ:Census V){n:Side}(P:RG.Rep G n) where
  s : Γ.Mode
  marked : s.val.Nonempty
  shellx : Seal n
  term : Config G n → ℂ
  chip : ℂ

namespace Page
variable (u:Page Γ P)

structure Entry (o:Positions V n)(v:ℝ) :Prop where
   stubs : ∀ i∈u.s.val,o.stub i ⊆ Seal.scope P u.shellx
   -- pre-mask regular. (no projection constraints here)
   opens (s:Support n)(h:u.shellx=.inl s) : P.p.Regular s u.term∧∀ j∈u.s.val,P.p.supBounds (o.origin j) s u.term v
   -- inherited forced partner on indicated true label
   closes (k:ℕ)(h:u.shellx=.inr k): GaugeInvariant u.term ∧ Measurable u.term ∧ UsesFinal P.p.threshold (P.activities.forced k).support u.term ∧
        ∀ U:Config G n,‖u.term U‖ ≤ v ∧ (u.term U≠0 →(P.activities.forced k).eligible P.p.threshold U)

/-- price of either kind before the real-valued leaf split. -/
def due (w:V→ℝ)(v:ℝ) := Poly.toll w u.s * ‖u.chip‖ * v

def ready : Config G n →ℂ := u.shellx.elim (fun s=> masked P.p.threshold s u.term) (fun _=>u.term)

def point (φ:ℂ) U:= Poly.send u.s (φ * (u.ready U*u.chip))
def aroma (φ:ℂ) U:= u.shellx.elim (fun _=> u.point φ U) (fun _=> 0)
def payment (φ:ℂ) U i:= u.shellx.elim (fun _=>0) (fun k:ℕ=>if k=i then u.point φ U else 0)

variable {o:Positions V n}{v:ℝ}(h:u.Entry o v)
include h
lemma nonneg : 0 ≤ v:=by
   cases e:u.shellx with
   | inl i=> obtain ⟨j,hj⟩:= u.marked; exact ((h.opens i e).2 j hj).1
   | inr k=> exact (norm_nonneg _).trans ((h.closes k e).2.2.2 1).1
end Page

variable (q:I→Page Γ P)(x:Positions V n)(v:I→ℝ)(w:V→ℝ)

structure MenuSafe (t:ℝ):Prop where
  each : ∀ i,(q i).Entry x (v i)
  radius : ∀ i,0<w i
  hit : Ac.Hit (fun i=>Seal.scope P (q i).shellx) P.p.B (fun i=>(q i).due w (v i)) (P.p.supportExponent-4) t

variable [Fintype I]

def essence [Fintype V] (header:V→ℂ)(φ:I→ℂ)(U:Config G n):Poly Γ:=
   let f:= Mach Γ header +∑ i,(q i).aroma (φ i) U
   let g (j:ℕ):= (Poly.bead Γ) (↑(P.activities.K j U):ℂ)+∑ i,(q i).payment (φ i) U j
   (Real.exp (P.exponent U):ℂ) • (Poly.pass f * ∑' p:Finset ℕ, if P.activities.admissible P.p U p then ∏ i∈p,g i else 0)

/-! ## Real-imaginary interface to thermal leaves -/
private def dye : Bool→ ℂ | false=>1 | true=>Complex.I
private def extract (p:Bool)(v:ℂ):ℝ:=if p then v.im else v.re
private lemma transparent (v:ℂ)(b:Bool) : ‖extract b v‖ ≤ ‖v‖:=by cases b <;> simp only [extract,Bool.false_eq_true,↓reduceIte,Real.norm_eq_abs]; exacts [Complex.abs_re_le_norm _,Complex.abs_im_le_norm _]
private lemma gather (v:ℂ): (extract false v:ℂ)*(dye false)+(extract true v:ℂ)*(dye true)=v:=by simp [extract,dye]

variable {t:ℝ}(A:Menu.Arsenal P)(h:MenuSafe q x v w t)
-- regular unused key allocated from Arsenal on that ACTUAL history at exact complete support.
-- choice(key) depends on support only.
private def selectReg (p:Support n) :ℕ:= if hx:p.Nonempty then (A.dry p hx).choose else 0
private def wing (p:Seal n) : Wing:= p.elim (fun i=> .logKey (selectReg A i)) Wing.gasKey
omit [Fintype I] in
include A h in
private lemma linked (i:I): let θ:= wing A (q i).shellx; θ.support P=Seal.scope P (q i).shellx ∧ θ.blank P:=by
   intro θ; unfold θ; let u:= q i
   have ht : (Seal.scope P (q i).shellx).Nonempty:=by obtain ⟨j,hj⟩:=u.marked; exact ⟨_,(h.each i).stubs j hj (x.mem _)⟩
   cases e:(q i).shellx with
   | inl p=> rw [e] at ht; change p.Nonempty at ht; change (P.activities.reg (selectReg A p)).support=p∧P.activities.E _=0; unfold selectReg; rw [dif_pos ht]; exact (A.dry p ht).choose_spec
   | inr _=> exact ⟨rfl,trivial⟩

set_option quotPrecheck false
local notation "φ" i => wing A (q i).shellx

def card (i:I)(b:Bool):Menu.Hat Γ P where
   M:= {
     turn:= (φ i)
     ingredient:= extract b ∘ (q i).ready
     weight:= v i
     scopedR:= by
       rw [(linked q x v w A h i).1]; unfold Page.ready; cases e:(q i).shellx with
       | inl s=> exact fun U V hV hd=> congr_arg (extract b) (Local.uses_mask _ ((h.each i).opens s e).1.sites U V hV hd)
       | inr k=> exact fun U V hV hd=> congr_arg (extract b) (((h.each i).closes k e).2.2.1 _ _ hV hd)
     grant:= by
       intro U he; unfold wing; unfold Page.ready at he; cases e:(q i).shellx with
       | inl s=>
         have hp := (linked q x v w A h i).1; rw [e] at hp; rw [e] at he
         change Healthy _ (P.activities.reg (selectReg A s)).support U; rw [show (P.activities.reg _).support=s from hp]; by_contra hx; exact he (by simp [masked,hx,extract])
       | inr k=>
         rw [e] at he; exact (((h.each i).closes k e).2.2.2 U).2 (fun H=>he (by simp [H,extract]))
     blank:= (linked q x v w A h _).2
     glows:= by
       unfold Page.ready; cases e:(q i).shellx with
       | inl s=> exact fun g U=> congr_arg (extract b) (Local.invariant_mask ((h.each i).opens s e).1.symmetry _ _ g U)
       | inr k=> exact fun g U=> congr_arg (extract b) (((h.each i).closes k e).1 g U)
     earn:=by
        intro U; apply (transparent _ _).trans
        unfold Page.ready; cases e:(q i).shellx with
        | inl s=>
          by_cases he: Healthy P.p.threshold s U
          · obtain ⟨j,hj⟩:= (q i).marked; change ‖masked _ _ _ U‖ ≤_; rw [masked_eq _ _ _ _ he]; exact (((h.each i).opens s e).2 j hj).2 U he [] (by simp) (by simp)
          change ‖masked _ _ _ U‖ ≤_; rw [masked_ne _ _ _ _ he,norm_zero]; exact Page.nonneg _ (h.each i)
        | inr k=> exact (((h.each i).closes _ e).2.2.2 U).1
     borel:=by
        apply (show Measurable (extract b) from (by
            unfold extract; cases b; exact Complex.continuous_re.measurable; exact Complex.continuous_im.measurable)).comp
        unfold Page.ready; cases e:(q i).shellx with
        | inl s=> exact masked_measurable _ _ _ ((h.each i).opens s e).1.borel
        | inr k=> exact ((h.each i).closes _ e).2.1 }
   s:= (q i).s
   shiny:= (q i).marked
   charge:= dye b*(q i).chip

def costume : Bool × I → Menu.Hat Γ P:= fun p=> card q x v w A h p.2 p.1

set_option quotPrecheck false
local notation "F!"=> costume q x v w A h

include h
lemma price_cards : Menu.Offer x.origin (F!) w P.p.B (P.p.supportExponent-4) (t+t)∧ ∀ i:Bool × I,∀ j∈ ((F!) i).s.val,x.stub j⊆ ((F!) i).M.crest:=by
   have he(i:Bool × I)(j)(hj:j∈ ((F!) i).s.val): x.stub j ⊆ ((F!) i).M.crest:=(by change _⊆ (φ i.2).support _; rw [(linked q x v w A h _).1]; exact (h.each i.2).stubs _ hj)
   refine ⟨⟨fun i k hk=> ?_,fun a=>?_⟩,he⟩
   · obtain ⟨j,hj,rfl⟩:=mem_image.mp hk; exact he _ _ hj (x.mem _)
   have hx(i:Bool×I): ((F!) i).M.crest=Seal.scope P (q i.2).shellx:= (linked q x v w A h i.2).1
   have hh(k:Bool×I): fare ((F!) k) w=(q k.snd).due w (v k.snd):=by unfold Menu.fare sumFee Page.due; change _ * ‖dye k.1*_‖ * _=_; rw [norm_mul,show ‖dye k.1‖=1 from by cases k.1 <;> simp [dye],one_mul]; rfl
   refine ⟨fun i=> ?_,Summable.of_finite,?_⟩
   · simp only [hx,hh] ; exact (h.hit a).1 _
   rw [tsum_fintype,Fintype.sum_prod_type]; simp_rw [hx,hh]
   rw [Fintype.sum_bool]; have hp:=(h.hit a).2.2; rw [tsum_fintype] at hp; exact add_le_add hp hp

open MenuBridge Extra.Trajectories
variable [Fintype V]{σ b c ζ ξ:ℝ}
-- combine both real sides exactly, then use old pinned barcode relation with Kunt not only under integration
variable (hf:P.Lawful σ c ζ b ξ)
include hf
set_option maxHeartbeats 220000 in
lemma pegs (read:I→(V→T)→ℂ)(header:V→(V→T)→ℂ)(viewX:V→T) :
    essence q (fun i=> header i viewX) (fun i=>read i viewX)=offered (F!) (read ∘ Prod.snd) header viewX:=by
    let t:= vital (F!) (read ∘ Prod.snd) viewX
    funext U
    let u i:=read i viewX; let f:= fun i=> Page.aroma (q i) (u i) U; let z j i:=Page.payment (q i) (u i) U j
    have hod(j:I):Menu.odour (t (true,j)) U +Menu.odour (t (false,j)) U= f j:=by
      unfold f Page.aroma; cases e:(q j).shellx with
      | inl k=>
        change Poly.send _ (MergeProof.prose _ U*_)+Poly.send _ (MergeProof.prose _ U * _)=_
        let V:= (q j).ready U; let s:=(q j).s; let d:=(q j).chip
        have hp (b:Bool):MergeProof.prose (t (b,j)).M U=(↑(extract b V):ℂ):=by
           unfold MergeProof.prose; rw [show (t (b,j)).M.turn= .logKey (selectReg A k) from (by change Sum.elim _ _ (q j).shellx=_; rw [e]; rfl)]; rfl
        change Poly.send s (MergeProof.prose (t (true,j)).M U *(dye true*d*u j))+Poly.send s (MergeProof.prose (t (false,j)).M U*(dye false*d*u j))=Poly.send s (u j*(V*d))
        rw [hp,hp, ← send_add]; congr 1; rw [show u j*(V*d)=((extract false V:ℂ)*dye false+(extract true V:ℂ)*dye true)*(d*u j) from (by rw [gather]; ring)]; ring
      | inr k=>
        have hp (b:Bool):MergeProof.prose (t (b,j)).M U=(0:ℂ):=by unfold MergeProof.prose; rw [show (t (b,j)).M.turn= .gasKey k from (by change Sum.elim _ _ (q j).shellx=_; rw [e]; rfl)]
        unfold Menu.odour; rw [hp,hp]; simp
    have hb(j:ℕ): Poly.bead Γ (P.activities.K j U:ℂ)+∑ i,z j i=Kunt t j U:= by
       unfold Kunt rush; rw [Fintype.sum_prod_type,Fintype.sum_bool,← sum_add_distrib]; apply congr_arg (_+·); apply Finset.sum_congr rfl; intro i _
       have hp(b:Bool): WKey (t (b,i))= wing A (q i).shellx:=rfl
       unfold z Page.payment; rw [hp,hp]; cases e:(q i).shellx with
       | inl p=>change (0:Poly Γ)=(if Wing.logKey _ = .gasKey j then _ else _)+(if Wing.logKey _ = .gasKey j then _ else _); simp
       | inr k=>
         change (if k=j then _ else _)=(if Wing.gasKey k = .gasKey j then _ else _)+(if Wing.gasKey k = .gasKey j then _ else _)
         by_cases hi:k=j; swap; · simp [hi]
         rw [if_pos hi,if_pos (congr_arg Wing.gasKey hi),if_pos (congr_arg Wing.gasKey hi),Menu.varnish,Menu.varnish]
         let V:= (q i).ready U; let s:= (q i).s; let d:= (q i).chip
         change Poly.send s (u i * (V*d))=Poly.send s (↑(extract true V)*(dye true*d*u i))+Poly.send s (↑(extract false V)*(dye false*d*u i))
         rw [←send_add]; congr 1; calc
           u i * (V*d)= ((extract false V:ℂ)*dye false+(extract true V:ℂ)*dye true)*(d*u i):=by rw [gather]; ring
           _=_:=by ring
    unfold offered GapsLocal.Full.given essence
    change _= Poly.pass (Mach Γ _)* ((Real.exp (P.exponent U):ℂ) • (Poly.pass (∑ i, odour (t i) U)*MergeProof.Accent.field (fun p=> bar P.activities Γ U p+∑ i,fragrance (t i) U p) _))
    have hr :(∑ i,odour (t i) U)=∑ i,f i:=by rw [Fintype.sum_prod_type,Fintype.sum_bool,←sum_add_distrib]; exact sum_congr rfl (fun i _=> hod i)
    have ho : (∑ i,f i).part Γ.quiet=0:=by
      rw [Poly.part_sum]; apply sum_eq_zero; intro i _; unfold f Page.aroma; cases (q i).shellx
      next S=> simp only [Sum.elim_inl,Page.point,Poly.part_send]; exact if_neg (fun e=>(q i).marked.ne_empty (congr_arg Subtype.val e.symm))
      next S=> exact Poly.part_nil _
    have hM : (Mach Γ (fun i=>header i viewX)).part Γ.quiet=0:=MergeProof.Accent.mute Γ _
    let m0:=Mach Γ (fun i=>header i viewX); let e:=Real.exp (P.exponent U)
    change m0.part Γ.quiet=0 at hM
    change (e:ℂ) • (Poly.pass (m0+∑ i,f i)*∑' p:Finset ℕ, if P.activities.admissible P.p U p then ∏ j∈p, (Poly.bead Γ (P.activities.K j U:ℂ)+∑ i,z j i) else 0) =Poly.pass m0*((e:ℂ) • _)
    rw [mul_smul_comm,←mul_assoc,hr,← Extra.Trajectories.pass_add hM ho] -- m0 syntactic at hM unfold
    apply congr_arg ((e:ℂ) • (Poly.pass (m0+∑ i,f i)*·))
    have hφ(i): (∑ j,fragrance (t j) U i)=board t i U:= (patron t U i).symm
    simp_rw [hφ,hb]; rw [← Menu.win t hf U, Accent.rock_out _ _ _ _ h.radius (Menu.fence t hf h.radius U).1]
end YM.FVA1
