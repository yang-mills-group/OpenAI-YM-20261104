import YangMills.WilsonProof.NativeSupport.JointMountedCaps
import YangMills.WilsonProof.NativeSupport.NativeBoardAdmission
import YM.MergeProof.Tanger

/-! Mount both proper sheets together on the same original native ticket.
The chosen regular rows are blank on every reserved board. The same
individual hats carry the inflated and full-exponent old invoices. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil
open Progress.DirectedRecipe Planned.GuardedAtom
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V : Type} [DecidableEq V] {B:Census V} {G:Gauge} {f:Side} {R:Rep G f}
variable {w:V→ℝ} {d a b:ℝ} {o:V→Site f}
variable {K:Support f → Config G f→Poly B} {F:Box f → Config G f→Poly B}

theorem dock_caps (reserved : HasSlots R.p R.activities) (h : RGGapR2.Rough.Ledger o K F R.p.threshold)
    (he : Towed w id K R.p.B d a) (hq : Towed w Prod.fst F R.p.B d b) (hw : ∀ i,0<w i)
    (old : Finset B.Mode) (E : Support f → B.Mode → ℝ) (C : Box f → B.Mode → ℝ)
    (eprice : ∀ i U p,p∈old → ‖(K i U).part p‖≤E i p)
    (cprice : ∀ i U p,p∈old → ‖(F i U).part p‖≤C i p) :
    ∃ q : (VividId K ⊕ VividId F) → Hat B R,
      Offer o q w R.p.B d (2*a+2*b) ∧
      (∀ j (Z:Rep G f),HasSlots Z.p Z.activities → (q j).M.turn.blank Z) ∧
      (∀ U,∑ j,odour (q j) U=∑ i,K i U) ∧
      (∀ i U,∑ j,fragrance (q j) U i=F i U) ∧
      (∀ i : VividId K,(q (.inl i)).s=i.2.1.val) ∧ (∀ i : VividId F,(q (.inr i)).s=i.2.1.val) ∧
      ∀ v : V→ℝ,(∀ j,0<v j) →
       (∀ i (p : {s : B.Mode // Vivid K i s}),p.val∈old →
          (∑ j:Bool,sumFee (q (.inl ⟨i,p,j⟩)) v*load (q (.inl ⟨i,p,j⟩)).M) ≤ 2*R.p.mass i (Poly.toll v p.val*E i p.val)) ∧
       (∀ i (p : {s : B.Mode // Vivid F i s}),p.val∈old →
          (∑ j:Bool,sumFee (q (.inr ⟨i,p,j⟩)) v*load (q (.inr ⟨i,p,j⟩)).M) ≤ 2*R.p.mass i.1 (Poly.toll v p.val*C i p.val)) := by
   have hb(i): K i≠0→i.Nonempty:=by
      intro H; obtain ⟨U,hU⟩:= Function.ne_iff.mp H; obtain ⟨p,hp⟩:= Function.ne_iff.mp (show Poly.part (K i U) ≠ Poly.part 0 from (by intro g; exact hU g)); let y:= h.exp i; have ht: 1 ≤ p.val.card:= (by
         apply Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
         intro he; exact hp ((congr_arg ((K i U).part) (Subtype.ext he : p=B.quiet)).trans (y.sil _))); exact ((Finset.card_pos.mp (by omega : 0 < p.val.card)).image o).mono (y.toBorne.place _ _ hp)
   let k (i:Support f) := if hi:i.Nonempty then Blush.found hi.choose i hi.choose_spec else 0
   let g i:=Wing.logKey (k i)
   have hK (i)(live:K i≠0) : (R.activities.reg (k i)).support=i ∧ R.activities.E (k i)=0 := by
     let hi:=hb i live
     unfold k
     rw [dif_pos hi]
     exact ⟨congrArg (fun p=>p.support) (Blush.latch R hi.choose i hi.choose_spec reserved),reserved.regular _⟩
   have hv(i U)(he:K i U≠0): (g i).qualifies R U:=by change Healthy _ _ U; rw [(hK i (fun hh=> he (congr_fun hh U))).1]; exact ((h.exp i).permits U he)
   obtain ⟨N,hN,H,hn,nprice⟩:=mounted_caps (v:=w) hw (F:=K) (X:=id) (g:=g)
     (fun i hp=>hK i hp) hv (fun i=>(h.exp i).toBorne) (fun i=>(h.exp i).sil) he old E eprice
   have hd(i): F i≠0 → Sure i:=by intro hh; obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; exact ((h.flag i).1.permits U hU).2
   let keeper:=Guard.Keeper.sufficient reserved
   let L (i:Box f) := if hi:Sure i then keeper.code ((⟨i,hi.1,hi.2⟩ : StockTag f),0) else 0
   let l i:=Wing.gasKey (L i)
   have hF (i)(live:F i≠0) : barcode R.activities (L i)=i ∧ ∀ U,i.1∩RG.flags R.p.threshold U=i.2 →
       (R.activities.forced (L i)).eligible R.p.threshold U := by
     let hi:=hd i live
     let tag : StockTag f:=⟨i,hi.1,hi.2⟩
     have same : barcode R.activities (L i)=i := by unfold L; rw [dif_pos hi]; exact cardK keeper tag
     refine ⟨same,fun U flag=>?_⟩
     have ht : (R.activities.forced (L i)).support∩flags R.p.threshold U=(R.activities.forced (L i)).inventory := by
       rw [(Prod.mk.inj same).1,(Prod.mk.inj same).2,flag]
     refine ⟨ht,?_⟩
     unfold L at *
     rw [dif_pos hi] at *
     exact keeper.pass (tag,0) U ht
   have ht (i U)(he:F i U≠0): (l i).qualifies R U:=(hF i (fun hh=> he (congr_fun hh U))).2 U (((h.flag i).1.permits U he).1)
   obtain ⟨M,hM,hB,hm,mprice⟩:=mounted_caps (v:=w) hw (F:=F) (X:=Prod.fst) (g:=l)
     (fun i hp=>⟨(Prod.mk.inj (hF i hp).1).1,trivial⟩) ht (fun i=>(h.flag i).1.toBorne)
     (fun i=>(h.flag i).2) hq old C cprice
   let m:= Sum.elim N M
   have hp(x): (N x).M.turn= .logKey (k x.1):= (hN x).1; have ht(x): (M x).M.turn=.gasKey (L x.1):=(hM x).1
   have hk(i:VividId F):barcode R.activities (L i.1)=i.1:=(hF _ (fun H=> (show Vivid F i.1 i.2.1.val from i.2.1.property).elim (fun U hU=> hU (by rw [H]; rfl)))).1
   have hy(U x):odour (N x) U=amount (N x) U:=by unfold odour prose; rw [hp,varnish]
   have hx'(U x):odour (M x) U=0:=by unfold odour prose;simp [ht]
   have hz (U x i):fragrance (N x) U i=0:=by unfold fragrance entry; simp [hp]
   have hs(U x i):fragrance (M x) U i=if x.1=i then amount (M x) U else 0:=by unfold fragrance entry; rw [ht]; dsimp only; rw [hk]; split_ifs; exact (varnish ..).symm; simp
   have blankN (i:VividId K)(Z:Rep G f)(slots:HasSlots Z.p Z.activities) : (N i).M.turn.blank Z := by
     obtain ⟨U,hU⟩:=i.2.1.property
     have hi:=hb i.1 (fun z=>hU (by rw [z];rfl))
     rw [hp]
     change Z.activities.E (k i.1)=0
     unfold k
     rw [dif_pos hi]
     exact slots.regular _
   refine ⟨m,H.cross hB,?_,?_,?_,fun i=>(hN i).2,fun i=>(hM i).2,fun v hv=>⟨nprice v hv,mprice v hv⟩⟩
   · rintro (i|i) Z slots
     · exact blankN i Z slots
     · change (M i).M.turn.blank Z
       rw [ht]
       trivial
   · intro U
     unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl, Sum.elim_inr, hy,hx', Finset.sum_const_zero,add_zero]; rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> hn i U
   · intro i U
     unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl,Sum.elim_inr,hz,Finset.sum_const_zero,zero_add,hs]; rw [Fintype.sum_sigma,sum_eq_single i]
     · simpa only [↓reduceIte] using hm i U
     · intro j _ hj; simp only [hj,↓reduceIte,sum_const_zero]
     simp

end YM.Integration.InletSusceptibility.JointShadow
