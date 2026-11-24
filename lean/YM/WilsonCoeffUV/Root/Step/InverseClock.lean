import YM.WilsonCoeffUV.Thermo.CoarsePacking
import YM.WilsonCoeffUV.Root.Step.Ribbon
import YM.WilsonCoeffUV.Test.Axis
/-! # Touring the fine pivot; preparations & currency exchange. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n f L:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η : ℝ} {d:Distance U}{w:U}{p:Cover}

-- tolled panel packing gadget on pts only, no α Nonempty needed.
private def trial (p:Cover)(w:Site L)(y:dock Cover (Co L α) r): dock Cover (Co L Unit) (r+1):= Fin.cons (p,w,()) (fun i=>( (y i).1, (y i).2.1,()))
lemma hearth (p:Cover)(w:Site L)(y:dock Cover (Co L α) r): L.val*tread Bank.terrain p y≤ tread Bank.terrain (L.val • p+lift w) (panel L α ∘ y) + 8*L.val:=by
    have he:= cover_pack (trial p w y); unfold tread
    rw [show stud p y=_ from ?pr,show stud _ (panel L α ∘ y)=_ from ?qr]; exact he
    case pr=> exact funext fun i=> Fin.cases rfl (fun j=> by simp [stud,trial]) i
    case qr=>
       ext1 i; refine Fin.cases rfl (fun j=>?_) i
       simp only [stud,Function.comp_apply,Fin.cons_succ,trial]; rfl
private def trialV (w:Site n)(b:Site L)(y:dock (Site n) (Co L α) r) : dock (Site n) (Co L Unit) (r+1):= Fin.cons (w,b,()) (fun i=>((y i).1,(y i).2.1,()))
lemma hearthV (g:Ratio n f)(b:Site n)(w:Site g.count)(y:dock (Site n) (Co g.count α) r):g.count.val*tread (tor n) b y≤ tread (tor f) (g.embed b + wrap f (lift w)) ((splitCo g α).symm ∘ y)+8*g.count.val := by
    have he:= local_pack g (trialV b w y)
    have hu: stud b y=Prod.fst ∘ trialV b w y:= funext fun i=> Fin.cases rfl (fun j=>by simp [stud,trialV]) i
    have hz: stud (g.embed b + wrap f (lift w)) ((splitCo g α).symm ∘ y)= Prod.fst ∘ (splitCo g Unit).symm ∘ trialV b w y:= by
        ext1 i; refine Fin.cases rfl (fun j=>?_) i; simp only [stud, Function.comp_apply,Fin.cons_succ,trialV]; rfl
    unfold tread; rw [hu,hz]; exact he

lemma spentL (L:Side){k j:ℕ}(h:L.val*k≤ j+8*L.val)(hp:0≤σ) : Real.exp (-(σ/L.val)*j)≤ Real.exp (8*σ)*Real.exp (-σ*k) := by
  rw [← Real.exp_add,Real.exp_le_exp]; have he : (L.val:ℝ)>0:= by positivity
  rw [neg_div', div_mul_eq_mul_div,div_le_iff₀ he]
  have hh : (L.val:ℝ)*k≤j+8*L.val:= by exact_mod_cast h
  linarith only [mul_le_mul_of_nonneg_left hh hp]
variable [NormedAddCommGroup V]
lemma Cork.cipher {P:Ten V (Cloth α) r}{w:Site L}(h:Cork Bank.terrain (lift w) (σ/L.val) C P)(he:0≤σ) : Cork Bank.terrain 0 σ (C*Real.exp (8*σ)) (turnTen (panel L α).symm P):=by
    refine ⟨mul_nonneg h.1 (by positivity),fun x=> (h.2 (panel L α ∘ x)).trans ?_⟩
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h.1; apply spentL L _ he; simpa only [smul_zero,zero_add] using hearth 0 w x
lemma Cork.cipherV {P:Ten V (Co f α) r} (g:Ratio n f)(w:Site g.count)(h:Cork (tor f) (wrap f (lift w)) (σ/g.count.val) C P)(he:0≤σ) : Cork (tor n) (wrap n 0) σ (C*Real.exp (8*σ)) (turnTen (splitCo g α) P):=by
    refine ⟨mul_nonneg h.1 (by positivity),fun x=> (h.2 ((splitCo g α).symm ∘ x)).trans ?_⟩; rw [mul_assoc,map_zero]; apply mul_le_mul_of_nonneg_left _ h.1; apply spentL g.count _ he; simpa only [show g.embed 0=0 from map_zero g.root,zero_add] using hearthV g 0 w x
lemma Bends.ciphers {L:Side}{P:raw α V r}{F:Ten V (Cloth α) r}(w:Site L)(h:Bends (lift w) P F): Bends 0 (fun n=> turnTen (splitCo (ratioN L n) α) (P (n*L))) (turnTen (panel L α).symm F):=by
    obtain ⟨s,c,hs,H⟩:=h.price
    refine ⟨fun x=> ?_,s,c*Real.exp (8*s),hs,((multi_end L).eventually H).mono (fun n hn=> Cork.cipherV (ratioN L n) w (hn.mono (div_le_self hs.le (by exact_mod_cast L.property))) hs.le)⟩
    exact ((h.point (panel L α ∘ x)).comp (multi_end L)).congr fun n=> congr_arg (P (n*L)) (funext fun i=>panel_wrap (ratioN L n) (x i))

def revolve [AddGroup U] (v:U)(P:Ten V (U×α) r): Ten V (U×α) r:= fun x=> P (jog (-v) ∘ x)
lemma rev_league {U:Type*}{d:Distance U} [AddGroup U] (b:U)(e:∀ x y,d.gap (b+x) (b+y)=d.gap x y)(w:U)(x:dock U α r): tread d (b+w) x=tread d w (jog (-b) ∘ x):=by
   let y:= stud w (jog (-b) ∘ x); let z:= stud (b+w) x
   have hu i:z i=b+y i:= by
       refine Fin.cases rfl (fun j=> by simp [y,z,stud,jog]) i
   unfold tread league; change (Finset.univ.sup (fun i=> Finset.univ.sup (fun j=>d.gap (z i) (z j))))=Finset.univ.sup (fun i=> Finset.univ.sup (fun j=> d.gap (y i) (y j))) ; simp_rw [hu,e]
lemma Cork.turn {P:Ten V (Cloth α) r}(p:Cover)(h:Cork Bank.terrain 0 σ A P): Cork Bank.terrain p σ A (revolve p P):=⟨h.1,fun x=> by
   have he:= h.2 (jog (-p) ∘ x); rw [← rev_league p (fun x y=>by simp [Bank.terrain]),add_zero] at he; exact he⟩
lemma Bends.turn {P:raw α V r}{F:Ten V (Cloth α) r}(p:Cover)(h:Bends 0 P F): Bends p (fun n=> revolve (wrap n p) (P n)) (revolve p F):=by
   obtain ⟨s,a,ht,H⟩:= h.price; refine ⟨fun x=> (h.point (jog (-p) ∘ x)).congr ?_,s,a,ht,H.mono fun n hn=> ⟨hn.1,fun x=>?_⟩⟩
   · intro n; apply congr_arg (P n); ext1 i; rw [← map_neg]; exact fold_move n (-p) (x i)
   have he:=hn.2 (jog (-wrap n p) ∘ x); rw [← rev_league (wrap n p) (fun x y=>by simp [tor]),map_zero,add_zero] at he; exact he
variable [NormedSpace ℝ V][NormedAddCommGroup E][NormedSpace ℝ E]
lemma Cork.touch {P: Ten V (U×α) r}(H: V →L[ℝ] E)(h:Cork d w σ A P): Cork d w σ (‖H‖*A) (H ∘ P):=⟨mul_nonneg (by positivity) h.1,fun x=> (H.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.2 x) (norm_nonneg _)).trans_eq (by ring))⟩
lemma Bends.touch (H:V→L[ℝ] E){P:raw α V r}{F:Ten V (Cloth α) r}(h:Bends p P F): Bends p (fun n=> H ∘ P n) (H ∘ F):=by
   obtain ⟨s,a,ht,K⟩:= h.price; exact ⟨fun x=> H.continuous.continuousAt.tendsto.comp (h.point x),s,_,ht,K.mono fun n hn=> hn.touch H⟩
open Embroider

def soprano (P:Patch)(w:Site P.L)(D) : Vote D→L[ℝ] Vote D:= ContinuousLinearMap.precomp ℝ (foldWord P w D)
lemma budgetS (P:Patch)(w:Site P.L)(D) : ‖soprano P w D‖≤ 1:= by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro z; rw [one_mul]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (fold_bound ..))
end YM.WilsonCoeffUV.Soil
