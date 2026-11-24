import YM.RG01Estimate.Furrow
/-!
 # Combine Portal taps. t is full, d is projection candidate, c is remaining
 known estimation. Gap arithmetic computed on Ovens.Pipes & actual log signs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Fresco
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{hn:20<n.val}(Q:Pilgrim p n hn)
abbrev Main (n:Side) := ℕ ⊕ (ℕ ⊕ Seat n)
abbrev Soft (n:Side) := ℕ ⊕ Seat n
def allot (A B:ℕ→RegularAddress n)(P:Support n)(h: (0:Site n) ∈ P) : Main n→ RegularAddress n:= Sum.elim A (Sum.elim B (fun x=> x.reg P h))
def ink (A C:ℕ→ Config G n→ℝ) (Z:Seat n→ Config G n→ℝ):Main n→ Config G n→ℝ:= Sum.elim A (Sum.elim C Z)
def loaf (A : Pipes G n) (P:Support n) : Soft n → Support n:= Sum.elim A.softer (fun x=> x.spread P)
def combine (A:Pipes G n) : Pipes G n where
   reg := allot A.reg A.reg Q.X (Q.anchored) ∘ numbering (Main n)
   kernel := A.kernel
   softer := loaf A Q.X ∘ numbering _
   sites i :=by change (loaf ..).Nonempty; rcases numbering (Soft n) i with i|i; exact A.sites i; exact ⟨i.2,(i.reg Q.X Q.anchored).anchor⟩

def iced (Δ : ℝ) (d:Tap G n): Soft n → Config G n → ℝ := Sum.elim d.logarithm (Pilgrim.ice G Δ Q)
def pour (Δ : ℝ) (d c b : Tap G n) : Tap G n where
   regular := ink d.regular c.regular (Pilgrim.tea G Δ) ∘ numbering (Main n)
   forced := b.forced
   logarithm := iced Q Δ b ∘ numbering _

variable {A:Pipes G n}{d c b : Tap G n}(hd:Fittings d A p)(hc:Fittings c A p)(hb:Fittings b A p)
include hd hc hb
lemma mixes (Δ: ℝ) : Fittings (pour Q Δ d c b) (combine Q A) p:=by
   let F:=ink d.regular c.regular (Pilgrim.tea G Δ)
   let Z:=allot A.reg A.reg Q.X Q.anchored
   let S:=iced Q Δ b; let Y:=loaf A Q.X
   have hf (i:Main n) : p.Regular (Z i).support (F i) ∧ F i 1=0 ∧ (Nonwrapping (Z i).support (Z i).site →∀ x y, IsAffineDirection (Z i).site x→ IsAffineDirection (Z i).site y→logHessian (F i) x y=0):= by
       rcases i with i|i|i
       · exact ⟨hd.regular.smooth _,hd.regular.at_flat _,hd.regular.vanish i⟩
       · exact ⟨hc.regular.smooth _,hc.regular.at_flat _,hc.regular.vanish i⟩
       obtain ⟨he,hB,h,hp⟩:= Q.tea_pays G Δ i
       exact ⟨he,hB,fun hν=>False.elim (h hν)⟩
   have hh (i:Soft n): GaugeInvariant (S i) ∧ UsesFinal p.threshold (Y i) (S i) ∧ Measurable (S i) ∧ (∀ V,S i V≠0→¬Healthy p.threshold (Y i) V):=by
       rcases i with i|i
       · exact ⟨hb.steady _,hb.looks i,hb.reads i,hb.visits i⟩
       obtain ⟨h,hP,hU,hT⟩:= Q.contract G Δ i; exact ⟨h,hP,hU,fun V=>(hT V).2⟩
   let N:= numbering (Main n); let K:=numbering (Soft n); let L:=combine Q A
   have hH := hb.support
   refine ⟨⟨fun _=> (hf _).1,fun _=> (hf _).2.1,fun _=> (hf _).2.2⟩, ?_,?_,fun _=>(hh _).2.2.2,fun _=>(hh _).1,fun _=>(hh _).2.1,
      fun _=>(hh _).2.2.1,?_⟩
   · exact ⟨hH.sym,hH.symtest,hH.meas,hH.meas_test,hH.reads,hH.reads_test,hH.permit⟩
   · intro s a
     obtain ⟨J⟩:= hb.moves s a; obtain ⟨J'⟩:=hd.moves s a; obtain ⟨I⟩:=hc.moves s a
     let U:Equiv.Perm (Main n):= Equiv.sumCongr J'.ep (Equiv.sumCongr I.ep (Seat.move s a))
     let p:= N.trans (U.trans N.symm); have he (i:ℕ): N (p i)=U (N i):= N.apply_symm_apply _
     have hg (x:Main n): (Z (U x)).site=affine s a (Z x).site ∧ (Z (U x)).support=(Z x).support.image (affine s a)∧ F (U x)=F x ∘ pull s a:= by
        rcases x with x|x|x
        · exact ⟨J'.reg_site x,J'.reg_support x,funext (J'.valuesE x)⟩
        · exact ⟨I.reg_site x,I.reg_support x,funext (I.valuesE x)⟩
        exact ⟨rfl,x.spread_move s a Q.X,show tea G Δ (Seat.move s a x) = tea G Δ x ∘ pull s a from by unfold tea; rw [x.view_move]; rfl⟩
     refine ⟨p,J.kp,fun i=>?_,fun i=>?_,J.forced_support,J.forced_inventory,J.forced_tests,fun i W=> ?_,J.valuesK⟩
     · change (Z (N (p i))).site=_; rw [he]; exact (hg _).1
     · change (Z (N (p i))).support=_; rw [he]; exact (hg (N i)).2.1
     change F (N (p i)) W=_; rw [he]; exact congr_fun (hg (N i)).2.2 W
   intro s a; obtain ⟨t,ht,hT⟩:= hb.carries s a
   let U:Equiv.Perm (Soft n):= Equiv.sumCongr t (Seat.move s a); let p:= K.trans (U.trans K.symm)
   have he (i:ℕ): K (p i)=U (K i):= K.apply_symm_apply _
   have hf (x:Soft n) : Y (U x) = (Y x).image (affine s a) ∧ S (U x)=S x ∘ pull s a:=by
       rcases x with x|x
       · exact ⟨ht x,funext (fun W=> hT W x)⟩
       exact ⟨x.spread_move s a Q.X,show ice G Δ Q (Seat.move s a x)= ice G Δ Q x ∘ pull s a from by unfold ice; rw [x.view_move]; rfl⟩
   refine ⟨p,fun i=>?_,fun V i=>?_⟩
   · change Y (K (p i))=_; rw [he]; exact (hf _).1
   change S (K (p i)) V=_; rw [he]; exact congr_fun (hf (K i)).2 V
end YM.RG01Estimate.Censor.Fresco
