import YM.MS.Tone.Pitch
/-!
# Bulk test into Fourier net. At all ranks and momenta. Growth later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau Momentum Paint Color Orient Mesh
open scoped Topology ContDiff
open Real
variable {G:Gauge}




inductive Mirrors : List (LightMode G QP)→ (Side→ List (LightMode G QP))→Prop where
| nil : Mirrors [] (fun _=>[])
| cons (a) (x:Side→QP)(p:QP)(hx:Tendsto x atTop (𝓝 p))(he:∀ i,x i∈proper i) l w (h:Mirrors l w): Mirrors ((a,p)::l) (fun i=> (a,x i)::w i)
variable {v:List (LightMode G QP)}{w:Side→List (LightMode G QP)}
namespace Mirrors
lemma rise (hv:Mirrors v w): ∀ i n,n∈w i→ n.2∈proper i := by
    induction hv with| nil=> simp| cons a x p hx he l w h ih=> intro i n hn; rcases List.mem_cons.mp hn with H|H; exact H ▸ he i; exact ih i n H
lemma net_to (hv:Mirrors v w): Tendsto (fun n=>net (w n)) atTop (𝓝 (net v)):= by
    induction hv with| nil=>exact tendsto_const_nhds| cons a x p hx he l w h ih=>simp only [net_cons]; exact hx.add ih
lemma prop_net (hv:Mirrors v w)(n:Side): net (w n)∈proper n := by
   induction hv with| nil=>exact ⟨0,(hz n).map_zero⟩| cons a x p hx he l w h ih=> simp only [net_cons]; obtain ⟨v,hv⟩:= he n; obtain ⟨u,hu⟩:=ih; exact ⟨v+u,(map_add ..).trans (congr_arg₂ _ hv hu)⟩
lemma multiplies (hv:Mirrors v w) (F:(Dot G Cover)): Tendsto (fun n=>run F (w n)) atTop (𝓝 (run F v)):= by
    induction hv generalizing F with
    | nil=> exact tendsto_const_nhds
    | cons a x p hx he l w h ih=>
       obtain ⟨s,hs⟩:=obliges F
       simp_rw [grows F hs]
       refine tendsto_finsetSum _ (fun i hi=> ?_); have hh := ((show Continuous (fun p:QP=>bill p (bornv (a,i))) by unfold bill pairing; fun_prop).tendsto p).comp hx
       exact hh.mul (ih (enter _ F))
lemma wish (v:List (LightMode G QP)): ∃ x, Mirrors v x := by induction v with| nil=> exact ⟨_,.nil⟩| cons a l ih=> obtain ⟨x,hx,he⟩:= idle a.2; obtain ⟨u,hu⟩:= ih; exact ⟨_,.cons _ x _ he hx _ u hu⟩
lemma net_wish (v:List (LightMode G QP))(h:net v=0): ∃ x, Mirrors v x∧∀ i,net (x i)=0:= by
    cases v with
    | nil=>exact ⟨_,.nil,fun _=>rfl⟩
    | cons a l=>
        obtain ⟨x,hx⟩:= wish l; have ht := hx.net_to.neg; rw [show -net l = a.2 from (eq_neg_of_add_eq_zero_left h).symm] at ht
        exact ⟨_, .cons a.1 (fun i=>-net (x i)) a.2 ht (fun i=>by obtain ⟨z,hz⟩:=hx.prop_net i; exact ⟨-z,by rw [map_neg,hz]⟩) l x hx, fun i=> by simp⟩
end Mirrors
lemma consent (F H:Dot G Cover)(h:BulkTest F H) (w:List (LightMode G QP))(he:net w=0): run F w=run H w:= by
    obtain ⟨z,hz,hg⟩:= Mirrors.net_wish _ he
    have hv : (fun n=> run F (z n)) =ᶠ[atTop] (fun n=> run H (z n)):= by
       refine h.mono (fun n hh=>?_); refine mul_left_cancel₀ (show (n.val:ℂ)^4≠0 from pow_ne_zero _ (Bloch.side_ne n)) ?_; dsimp only;
       rw [← consents F n _ (hz.rise n) (hg n),← consents H n _ (hz.rise n) (hg n)]; exact congr_arg (fun x=>shade (Mesh.hint n) x (z n)) (Subtype.ext hh)
    exact tendsto_nhds_unique_of_eventuallyEq (hz.multiplies F) (hz.multiplies H) hv
lemma legis (k:Signed)(i l) : (negateField k (G:=G) i)^2 * (l:ℂ)=l:=by
   unfold negateField; split; simp; rename_i i he; cases h:k.flip i <;> simp
lemma choral (F:(Dot G Cover))(h:stance F): SignedScope true (run F):= by
    intro k w he; let Y := fun l:List (LightMode G QP)=> (l.map (negateField k)).prod; have ht l:Y l * (Y l)=1:= by
       induction l with| nil=>simp [Y]| cons a l ih=> have h:= legis k (l:=1) a; simp only [Y,List.map_cons,List.prod_cons]; dsimp only [Y] at ih; rw [mul_mul_mul_comm (negateField _ _), ih,← _root_.sq, h] -- h typed sq*1
    rw [← consent _ _ (h k) _ (by rw [repose,he rfl,Signed.act_zero]), by_shift, ← mul_assoc, (show (w.map (negateField k)).prod*(w.map (negateField k)).prod=1 from ht _),one_mul] -- simplify
end YM.MS.Tone
