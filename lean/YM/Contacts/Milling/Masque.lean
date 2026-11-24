import YM.Contacts.Milling.Kindle
import YM.Next.STATIONARY.Films.LeadingRay
import YM.Next.STATIONARY.Loops.Curvature
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {α β X Y :Type}{n m:Side}{t k j:ℕ}{b:ℝ}{G:Gauge}{F:House X}
private def recital [Fintype X](F: Field (Fin k) X) : Tensor.T (Corn X) ℝ k:= { recording F with
   cont:= by
      change Continuous (fun p=>recording F p); simp_rw [recording_apply]; apply continuous_finsetSum; intros; fun_prop }
lemma recital_exact [Fintype X](f:Corn X→ℝ)(F: Field (Fin k) X)(hF:Poem F)(hf: AnalyticAt ℝ f 0)(hp:∀ x,jet f k x=design F x): Tensor.coeff f k 0 = recital F:= by
  refine Tensor.ext_diag _ _ (Tensor.coeff_symm hf.contDiffAt) (fun v e=> ?_) (funext fun x=>?_)
  · change recording _ (v ∘ e)=recording _ v; simp only [recording_apply]; rw [← Equiv.sum_comp (Equiv.arrowCongr e.symm (Equiv.refl _))]; -- evaluates at ??? LHS compose x∘e if domain e.symm yes
    apply sum_congr rfl; intro i _; rw [show Equiv.arrowCongr e.symm (Equiv.refl X) i=i∘e from rfl,hF e]; congr 1; apply Equiv.prod_comp e (fun j=> v j (i j))
  change jet f k x=recording F _; rw [hp, recording_apply,design_spec]; apply sum_congr ?_; swap; · congr!
  exact fun _ _=> mul_comm ..
lemma affixed [Fintype X][DecidableEq X](f:Corn X→ℝ)(F: Field (Fin k) X)(hF:Poem F)(hf:AnalyticAt ℝ f 0)(hp:∀ x,jet f k x=design F x): noteAt f k=recording (fun x=>(F x:ℂ)):= by
   apply enlarge_unique; intro v; rw [note_real,recital_exact f F hF hf hp]; change ((recording F v:ℝ):ℂ)=recording _ _; rw [recording_apply,recording_apply]; push_cast; rfl

def mask (F:Field (Fin (t+1)) (Node (Loc G 1))): Picture G t := fun i x => Laurent.read (pale (extract F (fun a=>(x a,i a))))
lemma shadow_face {s:ℝ≥0} (F:Field (Fin (t+1)) (Node (Loc G 1)))(b:ℝ)(h:Pulse.Rooted (terrain s _) F b) (hs:0<s): let η:ℝ:= (s:ℝ)/((t:ℝ)+1); ∀ i j, Firm η b (mask F i j):= by
   intro η i j; let μ:ℝ≥0:= ⟨η,by unfold η; positivity⟩; have he : 0<(s:ℝ):=hs; apply Firm.of_series (invest (export_price (η:=μ) h (fun a=>(j a,i a)) ?_)) (by change (0:ℝ)< η; unfold η; positivity); change (t:ℝ)* η≤_; unfold η; field_simp; linarith -- η not lifted rest
lemma holdF (P:X→Y)(w:Y→ℂ){F:X→ℝ}{G:Y→ℝ}(h:Scroll P F G)(hp:Summable F) [Fintype Y]: ∑ y:Y,w y*(G y:ℂ)=∑' x:X,w (P x)*(F x:ℂ):= by
   let f x:=w (P x)*(F x:ℂ)
   have hv i : cram P f i=w i*(G i:ℂ):= by rw [h]; unfold cram; rw [Complex.ofReal_tsum,← tsum_mul_left]; apply tsum_congr; intro b; simp [f,b.property];
   obtain ⟨D,hD⟩:= (Set.finite_range (fun y=>‖w y‖)).bddAbove; have he: Summable f:=by apply Summable.of_norm; refine ( (summable_abs_iff.mpr hp).mul_left D).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=>?_); unfold f; rw [norm_mul]; rw [Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hD ⟨P i,rfl⟩) (abs_nonneg (F i))
   have ht: tsum (cram P f)=tsum f := (bulky P he).tsum_eq; rw [tsum_fintype] at ht; simp_rw [hv] at ht; exact ht
-- for each anchor: exact plane transform at momentum tuple.
private def anchoredQ (p:Breed t (Site m))(a:Breed t (Dye G))(x: Breed t (Co m (Dye G))):ℂ:= ∏ i, relay (p i) (a i) (x i)
variable {P:Field (Fin (t+1)) (Node (Dye G))}{s:ℝ≥0}
private def bookK (z:Cover)(a:Breed t (Dye G))(v:Tailor t): Locked (Node (Dye G)) (0:Fin (t+1)) (z,a 0):= ⟨publish z a v,by simp [publish,legLane]⟩
private lemma mismatch {u: Breed t (Node (Dye G))}(j: Fin (t+1))(p:Breed t (Site m))(a:Breed t (Dye G))(h:(u j).2≠a j) : anchoredQ p a (lower m ∘ u)=0:= Finset.prod_eq_zero (mem_univ j) (by simp [relay,tune,Pi.single_apply,lower,h])
private lemma bookish (h:∀ a,Mirrored (backpack a) P)(p:Breed t (Site m))(a:Breed t (Dye G))(z:Cover) :
   (∑' q:Locked (Node (Dye G)) (0:Fin (t+1)) (z,a 0), anchoredQ p a (lower m∘ q.val)*(P q.val:ℂ)) = cell (∑ i,p i) (wrap m z)* Laurent.read (pale (extract P a)) (outphase p):= by
   let g(q:Locked (Node (Dye G)) (0:Fin (t+1)) (z,a 0)):= anchoredQ p a (lower m ∘ q.val)*(P q.val:ℂ); let V:= bookK z a; have hv : Injective V:= fun i j h=>by simpa only [V,bookK,deg_issue] using congr_arg (fun q:Locked (Node (Dye G)) (0:Fin (t+1)) (z,a 0)=> Spine.degree q.val) h
   change (∑' q,g q)=_; rw [← hv.tsum_eq, Laurent.read, ← tsum_mul_left]; swap; · intro x hx; suffices h: alphabet x.val=a by exact ⟨Spine.degree x.val,Subtype.ext (by dsimp [V,bookK]; convert retrieve x.val using 2; exact congr_arg Prod.fst x.property.symm; exact h.symm)⟩
                                                                                  by_contra hu; obtain ⟨j,hj⟩:=Function.ne_iff.mp hu; exact hx (by unfold g; rw [mismatch j p a hj,zero_mul])
   apply tsum_congr; intro q; unfold g V bookK anchoredQ; rw [show P (publish z a q)=extract P a q from ?_]; swap; · rw [extract, Function.comp_apply, ← h z (publish 0 a q)]; congr; ext1 i; simp [publish,backpack,add_comm]
   rw [gangRay,←cell_prod_hymn, smul_eq_mul,←mul_assoc,←prod_mul_distrib]; congr 1
   · apply prod_congr rfl; intro i _; simp only [relay,tune, lower,publish, Function.comp_apply,Pi.single_eq_same,mul_one]; rw [map_add,cell_add]
private def shore : ( (a:X) × Locked X (0:Fin (t+1)) a)≃(Fin (t+1)→X):= ⟨fun z=> z.2.val,fun u=> ⟨u 0,⟨u,rfl⟩⟩,fun ⟨a,u,H⟩=> by subst a; rfl, fun _=>rfl⟩
private lemma focused_book (p:Breed t (Site m))(a:Breed t (Dye G))(x:Site m){ε:ℝ≥0} {F:Field (Fin (t+1)) (Co m (Dye G))}(hp: Pulse.Rooted (terrain ε _) P b)(h: Shadow (lower m) P F)(he:∀ a,Mirrored (backpack a) P):
   (∑ q:Locked (Co m (Dye G)) (0:Fin (t+1)) (x,a 0), anchoredQ p a q.val*(F q.val:ℂ)) = cell (∑ i,p i) x* Laurent.read (pale (extract P a)) (outphase p):= by
    let ζ:= lift x; let Y (x: Site m):= ∑ q:Locked (Co m (Dye G)) (0:Fin (t+1)) (x,a 0),anchoredQ p a q.val*(F q.val:ℂ); have hh:wrap m ζ=x:= wrap_lift _; let i: Node (Dye G):= (ζ,a 0); have hw:lower m i=(wrap m ζ, a 0):= rfl; change Y x=_; rw [←hh]; refine Eq.trans (holdF _ (fun x:Locked (Co m (Dye G)) (0:Fin (t+1)) (lower m i)=> anchoredQ p a x.val) (h 0 i) (hp.raw 0 i|>.2.1.of_norm)) (bookish he p a ζ)
lemma masked (u:Link G m→ℝ)(hp: Pulse.Rooted (terrain s _) P b)(h: Poem P)(he:∀ a,Mirrored (backpack a) P)(hu:AnalyticAt ℝ u 0)(ht:∀ x,jet u (t+1) x=design (printShadow P m) x) : Recorded (mask P) u 0:= by
   apply (record_exact ..).mpr; intro p i b; let a: Breed t (Dye G):= fun j=>(b j,i j); let F:= printShadow P m; let X:= Co m (Dye G); let W(x: X):= ∑ q:Locked X (0:Fin (t+1)) x,anchoredQ p a q.val*(F q.val:ℂ); have ha:= heritage he m; rw [affixed u F (shadowEven ha h) hu ht,recording_apply]; calc
     _ = ∑ x : X,W x:= by erw [← Equiv.sum_comp (shore (X:=Lines G m 1) (t:=t)), Fintype.sum_sigma]; rfl
     _ = ∑ x:Site m, W (x,a 0) := by
        unfold X; rw [Fintype.sum_prod_type]; refine sum_congr rfl (fun j _=> Finset.sum_eq_single (a 0) ?_ ?_); swap; · simp
        intro k _ hk; apply sum_eq_zero; intro q _; unfold anchoredQ; rw [Finset.prod_eq_zero (i:= (0:Fin (t+1))) (mem_univ _) ?_,zero_mul]; rw [q.property]; simp [relay,tune,hk]
     _ = ∑ x:Site m, cell (∑ i,p i) x* mask P i b (outphase p):= sum_congr rfl fun j _=> focused_book p a j hp (printFeeds ha) he
     _ = _:= by
        rw [← Finset.sum_mul]; unfold collected; split
        next h=> rw [h]; simp_rw [cell_duality (0:Site m),cell_origin]; rw [sum_const]; simp
        next h=> rw [sum_cell h,zero_mul]
end
end YM.Contacts.Milling.Lumen
